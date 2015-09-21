package resolver.test;

import java.io.*;
import java.util.HashMap;
import java.math.BigInteger;
import static resolver.test.otherPackage.ResolverTestClass2.staticField;

public class ResolverTestMain {
   
    private static int staticField1 = 0;
    private /*@ spec_public @*/ int field1 = 0;
    private /*@ spec_public @*/ String field2 = "field2content";
    private /*@ spec_public @*/ ResolverTestClass1 field3 = null;
    private /*@ spec_public @*/ long fieldMultiple1, fieldMultiple2;
    private /*@ spec_public @*/ HashMap<Integer, String> field4 = new HashMap<Integer, String>();
    private /*@ spec_public @*/ BigInteger integer = new BigInteger(0);
    private /*@ spec_public @*/ java.math.BigDecimal decimal = new java.math.BigDecimal(0);
    private FileReader fr = null;
    private int[] arrayfield;
    
    public ResolverTestMain(int field1, String field2, ResolverTestClass1 field3) {
        this.field1 = field1;
        this.field2 = field2;
        this.field3 = field3;
    }
    
    public /*@ pure @*/ int methodNoParameters1() {
        return field1;
    }
    public /*@ pure @*/ String methodNoParameters2() {
        return field2;
    }
    public /*@ pure @*/ ResolverTestClass1 methodNoParameters3() {
        return field3;
    }
    
    /*@ normal_behavior
      @ assignable field1;
      @ ensures field1 == parameter1;
      @*/
    public boolean method1Parameter1(int parameter1) {
        Integer i = 1;
        field1 = parameter1;
        return true;
    }
    
    /*@ normal_behavior
      @ assignable field2;
      @ ensures field2 == methodNoParameters2();
      @*/
    public boolean method1Parameter2(String parameter2) {
        this.field2 = parameter2;
        return true;
    }
    
    /*@ normal_behavior
      @ assignable field3;
      @ ensures field3 == methodNoParameters3() && field3 == parameter3;
      @*/
    public boolean method1Parameter3(ResolverTestClass1 parameter3) {
        this.field3 = parameter3;
        return true;
    }
    
    /*@ normal_behavior
      @ requires parameterSameName1 != 0;
      @ assignable \nothing;
      @ ensures \result == methodSameName1Parameter1(field2);
      @*/
    public String methodSameName1Parameter1(int parameterSameName1) {
        return methodSameName1Parameter1(String.valueOf(parameterSameName1));
    }
    
    /*@ normal_behavior
      @ requires parameterSameName1 != 0;
      @ assignable \nothing;
      @ ensures \result == parameterSameName1;
      @*/
    public String methodSameName1Parameter1(String parameterSameName1) {
        return parameterSameName1;
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures \result == parameter1 + String.valueOf(parameter2);
      @*/
    public String method2Parameters1(String parameter1, int parameter2) {
        return parameter1 + String.valueOf(parameter2);
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures \result == method2Parameters1(parameter1, field1);
      @*/
    public double doSomething1(String parameter1) {
        return Double.valueOf(method2Parameters1(parameter1, 12));
    }
    
    /*@ normal_behavior
      @ assignable field1;
      @ ensures method1Parameter1(parameter1) == \result;
      @*/
    public boolean doSomething2(int parameter1) {
        return method1Parameter1(parameter1);
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures \result == method1Parameter2(parameter1);
      @*/
    public boolean doSomething3(String parameter1) {
        return method1Parameter2("doSomething3 - did something");
    }

    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures \result == true;
      @*/
    public boolean methodComplexParameter1(int parameter1) {
        return true;
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures true == methodComplexParameter1((int)field1 * (Integer)field1);
      @*/
    public int doSomething4() {
        return 5;
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures true == methodComplexParameter1(methodNoParameters1() * field1 * \result);
      @*/
    public int doSomething5() {
        return 10;
    }

    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures \result == field3.methodNoParameter1() &&
      @         \result == field3.method1Parameter4(2);
      @*/
    public int doSomething6() {
        return 2;
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures field3.field1 == Integer.valueOf(field3.field10) &&
      @         ResolverTestClass1.staticMethodNoParameter10() == 
      @         ResolverTestClass1.staticMethod1Parameter10(\result);
      @*/
    public int doSomething7() {
        return 0;
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures ResolverTestClass1.staticField10 == \result &&
      @         field3.field11 == methodSameName1Parameter1(\result);
      @*/
    public int doSomething8() {
        return 0;
    }
    
    /*@ normal_behavior
      @ assignable fieldMultiple1, fieldMultiple2;
      @ ensures fieldMultiple1 == fieldMultiple2;
      @*/
    public void doSomething9() {}
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures (\forall int i; 0 < i && i < arrayfield.length; arrayfield[i-1] <= arrayfield[i]);
      @*/
    public void doSomething10() {}
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures field3.getThis(field3).getThis(field3).getThis(field3) == field3 == \old(field3) == field3;
     */
    public void doSomething11() {}

    /*@ normal_behavior
      @ assignable this.field2;
      @ ensures String.valueOf(field2).equals(methodNoParameters3().getThis(field2).field10);
      @*/
    public int doSomething12(int field2) {
        int i = 0;
        
        /*@ maintaining i == arrayfield[x];
          @ decreasing arrayfield.length - x;
          @*/
        for(int x = 0; x < arrayfield.length; x++) {
            i = arrayfield[x];
        }
        return i;
    }
    
    /*@ normal_behavior
      @ assignable field4;
      @ ensures field4.containsKey(1) && 
                field4.put(1, "one") != null;
      @*/
    public HashMap<Integer,String> doSomething13() {
        field4.containsKey(1);
        field4.put(1, "one");
        return new HashMap<Integer, String>();
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures integer.add(integer) == integer
      @  && java.math.BigDecimal.valueOf(100) == decimal;
      @*/
    public void doSomething13() {
        decimal = java.math.BigDecimal.valueOf(100);
        integer = integer.add(integer);
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures fr.read() == \result;
      @*/
    public int doSeomthing14() {
        return fr.read();
    }
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures staticField == \result; 
      @*/
    public int testImportField() {
        return staticField;
    }
    
    /*@ normal_behavior
      @ assignable field3;
      @ ensures \result == ((ResolverTestClass1) field3.getThis()).field1;
      @*/
    public int castMethodAndThis() {
        field3 = new ResolverTestClass1();
        return ((ResolverTestClass1) field3.getThis(null)).field1;
    }
}