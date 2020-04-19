#lang forge

//6X6 board

/*
  This sig models an abstract square on the
  rush hour board.
*/
abstract sig Square {
    left: one Square,
    right: one Square,
    up: one Square,
    down: one Square
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
  Models a car object on the board.
  Contains a orientation that the
  car can move in. 
*/
abstract sig Car {
    ori: one Orientation

}

/*
  This models a state in the gameplay 
*/
sig State {
   redCarOri: one Orientation,
   redCarLoc: set Square,
   grayCarLoc: set Square,
   grayCarOri: one Orientation

}

/*
  Red car that has to escape the board. 
*/
one sig redCar extends Car {}

one sig grayCar extends Car {}


/*
  Initial state of the game. Must set up
  each squares neighboring squares.
*/

state[State] initState {
   setupBoard
  
   Horizontal in redCarOri
   Square10 in redCarLoc
   Square11 in redCarLoc
   
   Square12 in grayCarLoc
   Square22 in grayCarLoc
   Vertical in grayCarOri

}




/*
  Can we do separate files and include imports?
*/
pred setupBoard {
    no Square00.left
    no Square00.up
    Square00.down = Square10
    Square00.right = Square01
    /*Square01
    Square02
    Square03
    Square10
    Square11
    Square12
    Square13
    Square20
    Square21
    Square22
    Square23
    Square30
    Square31
    Square32
    Square33*/

}

/*
  Pred to setup the initial car's locations.
*/


//TODO
pred noOverlap {
    all s: State | (redCarLoc not in grayCarLoc) and (grayCarLoc not in redCarLoc)
}

pred gameRules{
    noOverlap

}










