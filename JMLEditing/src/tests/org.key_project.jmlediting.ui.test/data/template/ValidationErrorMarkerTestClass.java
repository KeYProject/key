package org.key_project.jmlediting.ui.test.marker;


public class ParseErrorMarkerTestClass {

 public static int sum (int a, int b, int c) {
    //@ decreasing a;
    return a + b + c;
 }
 
 public static int prod(int a, int b, int c) {
    //@ decreasing i;
    for(int i=0;i<2;i++){
       continue;
    }
    return a * b * c;
 }
   
}
