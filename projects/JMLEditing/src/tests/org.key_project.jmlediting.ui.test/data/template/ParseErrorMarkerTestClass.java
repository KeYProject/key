package org.key_project.jmlediting.ui.test.marker;


public class ParseErrorMarkerTestClass {

   /*@
   @ public normal_behavior
   @   assignable \noting;
   @ also
   @ public exceptional_behavir
   @   
   @*/
 public static int sum (int a, int b, int c) {
    return a + b + c;
 }
 
 /*@
   @ public behavior
   @   ensures \result == a * b * c;
   @   assignable \nothing;
   @*/
 public static int prod(int a, int b, int c) {
    return a * b * c;
 }
   
}
