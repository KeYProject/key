class Node {
    
  final static Node NIL = new Nil();

  boolean isRed;
  int key;
  int value;
  
  Node left, right;

  // the red-black tree properties
  //@ invariant (left == NIL && right == NIL) ==> !isRed;
  //@ invariant isRed ==> !(left.isRed || right.isRed);
  //@ invariant left.blackLeft() == right.blackRight;
  //@ invariant height() > left.height() && height() > right.height();
  
  Node (int key, int value){
      left = NIL;
      right = NIL;
      this.key = key;
      this.value = value;
  }
  
  /*@ pure @*/ int blackLeft (){
      return left.blackLeft()+(left.isRed?0:1);
  }
  
  /*@ pure @*/ int blackRight(){
      return right.blackRight()+(right.isRed?0:1);
  }
  
  //@ ensures \result >= 0;
  /*@ pure @*/ int height (){
      return 1+(left.height()>right.height?left.height:right.height);
  }
  
  final class Nil extends Node {
      Nil(){isRed=false;}
      int blackLeft(){return 0;}
      int blackRight(){return 0;}
      int height(){return 0;}
  }
  
}
