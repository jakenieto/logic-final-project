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

abstract sig Car{}
one sig Red extends Car{
   
}
one sig Gray extends Car{}

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
   redCarOri: one Orientation,
   redCarLoc: set Square,
   grayCarLoc: set Square,
   grayCarOri: one Orientation,
   toMove: one Car
   

}


/*
  Initial state of the game. Must set up
  each squares neighboring squares.
*/

state[State] initState {
  
   redCarOri = Horizontal
   redCarLoc = Square10 + Square11

   
   grayCarLoc = Square12 + Square22 
   grayCarOri = Vertical

   one toMove
 
   

}

state[State] finalState {
   redCarOri = Horizontal
   redCarLoc = END + Square12

   
   #(grayCarLoc) = 2
   grayCarOri = Vertical

   one toMove

}


transition[State] puzzle {
    redCarOri' = redCarOri
    grayCarOri' = grayCarOri
    #(redCarLoc') =  #(redCarLoc) 
    #(grayCarLoc') = 2

    toMove = Red implies {
        validMove[redCarLoc,redCarLoc',redCarOri]
        grayCarLoc' = grayCarLoc
    }
    toMove = Gray implies {
        validMove[grayCarLoc,grayCarLoc',grayCarOri]
        redCarLoc' = redCarLoc
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


//TODO
pred noOverlap {
    all s: State {
        all r: s.redCarLoc | r not in s.grayCarLoc
        all g: s.grayCarLoc | g not in s.redCarLoc 
    }
}

pred gameRules{
    noOverlap
    setupBoard
}

pred validLoc[loc: set Square,ori: one Orientation] {
    all s: loc {
        ori = Horizontal implies {
            one s2: (loc - s) | (s.left = s2 or s.right = s2)
        }
        ori = Vertical implies {
             one s2: (loc - s) | (s.up = s2 or s.down = s2)
        }

    }

}

pred validMove[startLoc: set Square, endLoc: set Square, ori: one Orientation] {
    ori = Horizontal implies{
        all s: startLoc {
            //Possible transitive closure like operation to do??
            all bs: (Square - (s.^(left + right))) | bs not in endLoc
            //all bs: (Square - (s.^(left + right) s.right + s + s.left.left + s.right.right + s.left.right + s.right.left)) | bs not in endLoc
        }

    }
    ori = Vertical implies {
        all s: startLoc {
            all bs: (Square - (s.^(up + down)))| bs not in endLoc
        }
    }
    
    validLoc[endLoc,ori]
    

}



trace<|State, initState, puzzle, finalState|> traces: linear {}

run<|traces|> gameRules for 3 State









