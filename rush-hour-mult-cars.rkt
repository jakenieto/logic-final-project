#lang forge

/**
  RUSH HOUR (MULTIPLE CARS)

  Implementation of the slide block logic puzzle game Rush Hour, in which you slide
  the blocking vehicles out of the way for the red car to exit. Instead of solely
  focusing on only two cars, this file is generalized so that more than one other
  blocking car is considered.
*/


//---------SIG DEFINITIONS---------//


/*
  This sig models an abstract square on the rush hour board.
*/
abstract sig Square {
    left: lone Square,
    right: lone Square,
    up: lone Square,
    down: lone Square
}

/*
  Identification of target car and blocking cars.
*/
abstract sig Color {}
one sig Red extends Color {}
one sig Other extends Color {}

/*
  This sig models a car in the game, which contains a color (to be able to specify
  the target car) and its orientation (specifying which direction it can move in).
*/
sig Car {
    color: one Color,
    ori: one Orientation
}


/*
  Actual instances of squares. There are 16 for a 4X4 board.
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
  Models the orientation that a car has relative to the board. This direction
  describes the possible direction of motion that the car can take. The two
  direction types are "horizontal" and "vertical".
*/
abstract sig Orientation {}
one sig Vertical extends Orientation {}
one sig Horizontal extends Orientation {}


/*
  This models a state in the gameplay. Each state keep track of the squares
  that each car is currently in, as well as a variable to store the next car
  to be moved (ensuring that the cars are moved one at a time).
*/
sig State {
    carLoc: set Car->Square,
    toMove: one Car
}


//---------STATE DEFINITIONS---------//


/*
  Initial state of the game. Must set up each squares neighboring squares,
  define the sizes that each car can take on, define the red car, the squares
  that each car exists within (and that they are valid), and one car that is
  is set to move next.
*/
state[State] initState {
    validCarSizes[carLoc]
    hasRedCar[carLoc]
    some carLoc
    validLoc[carLoc]
    one toMove
}

/*
  Final state of the game. Ensures that a red car must win (reach the end tile)
  in the final state, defines one car must still move at a time and each car's
  location must be valid.
*/
state[State] finalState {
    redCarWins[carLoc]
    one toMove
    validLoc[carLoc]
}


//------------GAME RULES------------//


//TODO
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
  Defines all of the squares of the board and their left, right, up and down
  squares.
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
  Ensures that for each state, none of the cars overlap -- none of the squares
  of a car exists in the carLoc squares of another car. 
*/
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

/*
  General set of game rules that ensures there is only one red car, and calls
  two of the other game-defining predicates -- noOverlap and setupBoard.
*/
pred gameRules{
   #(color.Red) = 1
   noOverlap
   setupBoard
}


//---------TRANSITION PREDICATES---------//


/*
  Defines each car to be at least of length 2.
*/
pred validCarSizes[carLoc: set Car->Square] {
    all c: Car | #(c.carLoc) >= 2

}

/*
  Ensures that there exists a red car (target car) that is colored red (which enables
  us to identify it during each transition), has horizontal orientation, is of size 2,
  and does begin on the end squares.
*/
pred hasRedCar[carLoc: set Car->Squares] {
    one c: Car {
        c.color = Red
        c.ori = Horizontal
        #(c.carLoc) = 2
        END not in c.carLoc
        Square12 not in c.carLoc
    }
}

/*
  Ensures that in the end state the red car exists on the two end squares.
*/
pred redCarWins[carLoc: set Car->Square] {
    all c: Car {
         c.color = Red implies {
            c.carLoc = END + Square12
        }
    }
}

/*
  Ensures that each car's current position is valid.
*/
pred validLoc[loc: set Car->Square] {
    all c: Car {
        all s: c.loc {
            // Two cases depending on the current car's orientation.
            c.ori = Horizontal implies {
                // Ensures that the car continues to remain connected.
                some s1:  (c.loc - s) | s1 = s.left or s1 = s.right
                // Allows for cars to move more than one square at a time.
                all s2: (c.loc - s) | s2 in s.^(left + right)
                // Disallows vertical squares from being accessed by a horizontal car.
                no s3: (c.loc - s) | (s.up = s3 or s.down = s3)
            }
            c.ori = Vertical implies {
                // Ensures that the car continues to remain connected.
                some s1:  (c.loc - s) | s1 = s.up or s1 = s.down
                // Allows for cars to move more than one square at a time.
                all s2: (c.loc - s) | s2 in s.^(up + down)
                // Disallows horizontal squares from being accessed by a vertical car.
                no s3: (c.loc - s) | (s.left = s3 or s.right = s3)
            }
        }
    }
}

/*
  Ensures that a car's position in the post state is valid.
*/
pred validMove[startLoc: set Car->Square, endLoc: set Car->Square,car: one Car] {
    // Two cases based on the car's orientation.
   car.ori = Horizontal implies {
        all s: car.startLoc {
            // Horizontal cars can only move into left or right squares on the same row.
            all bs: (Square - (s.^(left + right))) | bs not in car.endLoc
        }
    }
    car.ori = Vertical implies {
        all s: car.startLoc {
            // Vertical cars can only move into up or down squares in the same column.
            all bs: (Square - (s.^(up + down)))| bs not in car.endLoc
        }
    }   
    validLoc[endLoc]
}

pred optimal {
   one s: State | Square12 in (color.Red).(s.carLoc) and END in (color.Red).(s.carLoc)
   all s1,s2: State | s1 != s2 implies {s1.carLoc != s2.carLoc}
}


//------------GENERAL CHECKS------------//


/*
  Checks that a car doesn't have squares that exist diagonally / disconnected from its other ones.
*/
pred noDiagonal[loc: set Car->Square] {
      all c: Car {
        all sq: c.loc {
            // Two cases based on the car's orientation.
            c.ori = Horizontal implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                no s: (Square - (c.loc).^(left + right)) | s in c.loc
            }
            c.ori = Vertical implies {
                 // Makes sure no squares exist outside of the column of the current vertical car.
                no s: (Square - (c.loc).^(up + down)) | s in c.loc
            }
        }
    }
}


/*
  Checks that a car doesn't have squares that exist diagonally / disconnected from its other ones.
*/
pred sameLanes[loc: set Car->Square] {
      all c: Car {
        all sq: c.loc {
            // Two cases based on the car's orientation.
            c.ori = Horizontal and Square00 in (c.loc).^(right) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square00 or Square01 or Square02 or Square03 in c.loc
            }
            c.ori = Horizontal and Square10 in (c.loc).^(right) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square10 or Square11 or Square12 or Square13 in c.loc
            }
            c.ori = Horizontal and Square20 in (c.loc).^(right) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square20 or Square21 or Square22 or Square23 in c.loc
            }
            c.ori = Horizontal and Square30 in (c.loc).^(right) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square30 or Square31 or Square32 or Square33 in c.loc
            }
            c.ori = Vertical and Square00 in (c.loc).^(down) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square00 or Square10 or Square20 or Square30 in c.loc
            }
             c.ori = Vertical and Square01 in (c.loc).^(down) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square01 or Square11 or Square21 or Square31 in c.loc
            }
             c.ori = Vertical and Square02 in (c.loc).^(down) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square02 or Square12 or Square22 or Square32 in c.loc
            }
             c.ori = Vertical and Square03 in (c.loc).^(down) implies {
                // Makes sure no squares exist outside of the row of the current horizontal car.
                --no s: (Square - (c.loc).^(left + right)) | s in c.loc
                Square03 or Square13 or Square23 or Square33 in c.loc
            }
        }
    }
}


/*
  Checks that a car doesn't have squares that exist diagonally / disconnected from its other ones.
*/
pred sameOrientation[s: State] {
    all s2: State {
        s.(toMove.ori) = s2.(toMove.ori)
    }
}


/*
  General statement to verify that the algorithm is behaving as it should be (no cars become ill formed).
*/
pred wellFormedCars {
    all s: State {
        noDiagonal[s.carLoc]
        sameOrientation[s]
  
    }
}
            
trace<|State, initState, puzzle, finalState|> traces: linear {}

check<|traces|> {(gameRules and optimal) => wellFormedCars} for  2 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  3 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  4 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  5 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  6 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  7 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  8 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  9 State
check<|traces|> {(gameRules and optimal) => wellFormedCars} for  10 State


--trace<|State, initState, puzzle, finalState|> traces: linear {}
--run<|traces|> {gameRules optimal} for  8 State


//---------------TESTING---------------//


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




