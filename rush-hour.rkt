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
  This sig models an abstract square on the
  rush hour board.
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
abstract sig Car{}
one sig Red extends Car{}
one sig Gray extends Car{}

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
   redCarOri: one Orientation,
   redCarLoc: set Square,
   grayCarLoc: set Square,
   grayCarOri: one Orientation,
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
   redCarOri = Horizontal
   redCarLoc = Square10 + Square11
   grayCarLoc = Square12 + Square22 
   grayCarOri = Vertical
   one toMove
}

/*
  Final state of the game. Ensures that a red car must win (reach the end tile)
  in the final state, defines one car must still move at a time and each car's
  location must be valid.
*/
state[State] finalState {
   redCarOri = Horizontal
   redCarLoc = END + Square12
   #(grayCarLoc) = 2
   grayCarOri = Vertical
   one toMove
}


//------------GAME RULES------------//


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
        all r: s.redCarLoc | r not in s.grayCarLoc
        all g: s.grayCarLoc | g not in s.redCarLoc 
    }
}

/*
  General set of game rules that ensures there is only one red car, and calls
  two of the other game-defining predicates -- noOverlap and setupBoard.
*/
pred gameRules{
    noOverlap
    setupBoard
}


//---------TRANSITION PREDICATES---------//


/*
  Ensures that each car's current position is valid.
*/
pred validLoc[loc: set Square,ori: one Orientation] {
    all s: loc {
        // Two cases based on the car's orientation.
        ori = Horizontal implies {
            // Ensures that the each horizontal car only move one square to the right/left.
            one s2: (loc - s) | (s.left = s2 or s.right = s2)
        }
        ori = Vertical implies {
            // Ensures that the each vertical car only move one square to the up/down.
             one s2: (loc - s) | (s.up = s2 or s.down = s2)
        }

    }

}

/*
  Ensures that a car's position in the post state is valid.
*/
pred validMove[startLoc: set Square, endLoc: set Square, ori: one Orientation] {
    // Two cases based on the car's orientation.
    ori = Horizontal implies {
        all s: startLoc {
            // Horizontal cars can only move into left or right squares on the same row.
            all bs: (Square - (s.^(left + right))) | bs not in endLoc
        }
    }
    ori = Vertical implies {
        all s: startLoc {
            // Vertical cars can only move into up or down squares in the same column.
            all bs: (Square - (s.^(up + down)))| bs not in endLoc
        }
    }    
    validLoc[endLoc,ori]
}


trace<|State, initState, puzzle, finalState|> traces: linear {}
run<|traces|> gameRules for 3 State









