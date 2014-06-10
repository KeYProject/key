package testTermParserHeap;

class B {
  int f;
  //@ ghost int gf;
  //@ model int mf;
 
  //@ model int mmeth(int arg) { return 0; }
  
  int meth(int arg) { return 0; }
}
