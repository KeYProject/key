interface AbstractMap{

  //@ model int defaultValue;
  //@ model int[] contents;

  //@ axiom contents.length == 2147483647;
  //@ initially (\forall int i; 0 <= i; contents[i] == defaultValue);

  //@ requires key >= 0;
  //@ ensures contents[key] == value;
  void replace (int key, int value);

  //@ requires key >= 0;
  //@ ensures contents[key] == defaultValue;
  void remove (int key);

  //@ requires key >= 0;
  //@ ensures \result == contents[key];
  /*@ pure @*/ int lookup (int key);
}
