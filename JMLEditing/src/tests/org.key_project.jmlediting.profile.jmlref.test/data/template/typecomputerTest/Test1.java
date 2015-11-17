package typecomputer.test;

public class Test1 {
   
   //@ invariant true;
   //@ invariant 'c';
   //@ invariant 12;
   //@ invariant "string";
   //@ invariant true == booleanField;
   //@ invariant booleanField;
   //@ invariant 4.5;
   //@ invariant 5 * 4.3 * 10;
   //@ invariant 5 * intField;
   //@ invariant booleanField <==> true;
   
   //@ invariant true ==> booleanField;
   //@ invariant !booleanField2;
   //@ invariant (Object)stringField;
   //@ invariant intField < 10;
   //@ invariant ++intField;
   //@ invariant intField++;
   //@ invariant (15 + 16 + 17 + 18);
   //@ invariant 19 - (17 + 5.6 * 1 * 0.1);
   //@ invariant booleanField && booleanField2;
   //@ invariant booleanField || booleanField2;
   
   //@ invariant booleanField & booleanField2;
   //@ invariant booleanField ^ booleanField2;
   //@ invariant booleanField | booleanField2;
   //@ invariant 12 << 1;
   //@ invariant 2.5 >> 1;
   //@ invariant --floatField;
   //@ invariant ~intField;
   //@ invariant +floatField;
   //@ invariant booleanField == new Boolean();
   //@ invariant o = stringField = "someString";
   
   //@ invariant stringField = "someString";
   //@ invariant -doubleField;
   //@ invariant ((!booleanField));
   
   boolean booleanField;
   Boolean booleanField2;
   int intField;
   float floatField;
   double doubleField;
   String stringField;
   int[] intArrayField;
   Object o;
   
   
}