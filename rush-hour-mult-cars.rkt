#lang forge

//4X4 board

/*
  This sig models an abstract square on the
  rush hour board.
*/
abstract sig Square {
    left: lone Square,
    right: lone Square,
    up: lone Square,
    down: lone Square
}

abstract sig Color {}

one sig Red extends Color {}
one sig Other extends Color {}

sig Car{
    color: one Color,
    ori: one Orientation
}


/*
  Actual instances of squares. There are
  16 for a 4X4 board.
*/
one sig Square00 extends Square {}
one sig Square01 extends Square {}
one sig Square02 extends Square {}
one sig Square03 extends Square {}
one sig Square10 extends Square {}
one sig Square11 extends Square {}
one sig Square12 extends Square {}
one sig END extends Square {}
one sig Square20 extends Square {}
one sig Square21 extends Square {}
one sig Square22 extends Square {}
one sig Square23 extends Square {}
one sig Square30 extends Square {}
one sig Square31 extends Square {}
one sig Square32 extends Square {}
one sig Square33 extends Square {}

/*
  Models the orientation that a car has
  relative to the board. This direction
  describes the possible direction of motion
  that the car can take. The two direction
  types are "horizontal" and "vertical".
*/
abstract sig Orientation {}
one sig Vertical extends Orientation {}
one sig Horizontal extends Orientation {}


/*
  This models a state in the gameplay 
*/
sig State {
    carLoc: set Car->Square,
    toMove: one Car
   
   

}


/*
  Initial state of the game. Must set up
  each squares neighboring squares.
*/

state[State] initState {
    validCarSizes[carLoc]
    hasRedCar[carLoc]
    some carLoc
    validLoc[carLoc]
    one toMove
 

}

state[State] finalState {
    redCarWins[carLoc]
    one toMove
    validLoc[carLoc]
   

}


transition[State] puzzle {
    
    all car: Car {
        #(car.carLoc) = #(car.carLoc')
        car = toMove implies {
           validMove[carLoc,carLoc',car]
        }
        car != toMove implies {
             car.carLoc' = car.carLoc
        }

    }
    one toMove'
}


/*
  Can we do separate files and include imports?
*/
pred setupBoard {
    no Square00.left
    no Square00.up
    Square00.down = Square10
    Square00.right = Square01
    
    Square01.left = Square00
    no Square01.up
    Square01.down = Square11
    Square01.right = Square02

    Square02.left = Square01
    no Square02.up
    Square02.down = Square12
    Square02.right = Square03

    Square03.left = Square02
    no Square03.up
    Square03.down = END
    no Square03.right

    no Square10.left
    Square10.up = Square00
    Square10.down = Square20
    Square10.right = Square11

    Square11.left = Square10
    Square11.up = Square01
    Square11.down = Square21
    Square11.right = Square12

    Square12.left = Square11
    Square12.up = Square02
    Square12.down = Square22
    Square12.right = END

    END.left = Square12
    END.up = Square03
    END.down = Square23
    no END.right

    no Square20.left
    Square20.up = Square10
    Square20.down = Square30
    Square20.right = Square21

    Square21.left = Square20
    Square21.up = Square11
    Square21.down = Square31
    Square21.right = Square22

    Square22.left = Square21
    Square22.up = Square12
    Square22.down = Square32
    Square22.right = Square23

    Square23.left = Square22
    Square23.up = END
    Square23.down = Square33
    no Square23.right

    no Square30.left
    Square30.up = Square20
    no Square30.down 
    Square30.right = Square31

    Square31.left = Square30
    Square31.up = Square21
    no Square31.down 
    Square31.right = Square32

    Square32.left = Square31
    Square32.up = Square22
    no Square32.down
    Square32.right = Square33

    Square33.left = Square32
    Square33.up = Square23
    no Square33.down 
    no Square33.right 

}

/*
  Pred to setup the initial car's locations.
*/


pred validCarSizes[carLoc: set Car->Square] {
    all c: Car | #(c.carLoc) >= 2

}

pred hasRedCar[carLoc: set Car->Squares] {
  
    one c: Car {
        c.color = Red
        c.ori = Horizontal
        #(c.carLoc) = 2
        END not in c.carLoc
        Square12 not in c.carLoc
    }
        
    

}

pred redCarWins[carLoc: set Car->Square] {
    all c: Car {
         c.color = Red implies {
            c.carLoc = END + Square12
        }
    }


}

pred noOverlap {
   all s: State {
       all c1,c2: Car {
           c1 != c2 implies {
               all s1: c1.(s.carLoc) | s1 not in c2.(s.carLoc)
               all s2: c2.(s.carLoc) | s2 not in c1.(s.carLoc)
           }
           
       }
   }
}



pred gameRules{
   #(color.Red) = 1
   //#(carLoc) > 11
  // #(Car) = 4
   //all s: State | one c: Car | #(c.(s.carLoc)) > 3
   noOverlap
   setupBoard

}

pred validLoc[loc: set Car->Square] {
    all c: Car {
        all s: c.loc {
            c.ori = Horizontal implies {
                some s1:  (c.loc - s) | s1 = s.left or s1 = s.right
                all s2: (c.loc - s) | s2 in s.^(left + right)
                no s3: (c.loc - s) | (s.up = s3 or s.down = s3)
            }
            c.ori = Vertical implies {
                some s1:  (c.loc - s) | s1 = s.up or s1 = s.down
                all s2: (c.loc - s) | s2 in s.^(up + down)
                no s3: (c.loc - s) | (s.left = s3 or s.right = s3)
            }
        }
    }
}
//carLoc,carLoc',carOri,car

pred validMove[startLoc: set Car->Square, endLoc: set Car->Square,car: one Car] {
 
   car.ori = Horizontal implies{
        all s: car.startLoc {
            //Possible transitive closure like operation to do??
            all bs: (Square - (s.^(left + right))) | bs not in car.endLoc
            //all bs: (Square - (s.^(left + right) s.right + s + s.left.left + s.right.right + s.left.right + s.right.left)) | bs not in endLoc
        }

    }
    car.ori = Vertical implies {
        all s: car.startLoc {
            all bs: (Square - (s.^(up + down)))| bs not in car.endLoc
        }
    }
    
    validLoc[endLoc]
    

}

pred optimal {
   one s: State | Square12 in (color.Red).(s.carLoc) and END in (color.Red).(s.carLoc)
   all s1,s2: State | s1 != s2 implies {s1.carLoc != s2.carLoc}
}

pred noDiagonal[loc: set Car->Square] {
      all c: Car {
        all sq: c.loc {
            c.ori = Horizontal implies {
                no s: (Square - (c.loc).^(left + right)) | s in c.loc
            }
            c.ori = Vertical implies {
                no s: (Square - (c.loc).^(up + down)) | s in c.loc
            }
        }
    }
}

pred welformedCars {
    all s: State {
        noDiagonal[s.carLoc]
    }
 
}
            


--trace<|State, initState, puzzle, finalState|> traces: linear {}

--run<|traces|> {gameRules optimal} for  8 State


//testing
/*
inst discontinuous {
    State = State0 + State1 + State2 + State3 + State4 + State5 + State6 + State7 
    Car = Car1 + Car2 + Car3
    State1.carLoc = Car1->END0 + Car1->Square230 + Car2->Square010 + Car2->Square020 + Car3->Square110 + Car3->Square130
}

inst horizToVert {
    State = State0 + State1 + State2 + State3 + State4 + State5 + State6 + State7 
    Car = Car1 + Car2 + Car3
    State1.carLoc = Car1->END0 + Car1->Square230 + Car2->Square010 + Car2->Square020 + Car3->Square110 + Car3->Square210
}

inst vertToHoriz {
    State = State0 + State1 + State2 + State3 + State4 + State5 + State6 + State7 
    Car = Car1 + Car2 + Car3
    State3.carLoc = Car1->220 + Car1->Square230 + Car2->Square010 + Car2->Square020 + Car3->Square110 + Car3->Square120
}

inst overlap {
    State = State0 + State1 + State2 + State3 + State4 + State5 + State6 + State7 
    Car = Car1 + Car2 + Car3
    State6.carLoc = Car1->END0 + Car1->Square230 + Car2->Square010 + Car2->Square020 + Car3->Square120 + Car3->END0
}

test expect {
    discontinuousTest : {gameRules optimal} for discontinuous is unsat
    horizToVertTest : {gameRules optimal} for horizToVert is unsat
    vertToHorizTest: {gameRules optimal} for vertToHoriz is unsat
    overlapTest : {gameRules optimal} for overlap is unsat

}
*/
trace<|State, initState, puzzle, finalState|> traces: linear {}

/*
check<|traces|> {(gameRules and optimal) => welformedCars} for  2 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  3 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  4 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  5 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  6 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  7 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  8 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  9 State
check<|traces|> {(gameRules and optimal) => welformedCars} for  10 State
*/



