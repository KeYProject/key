package main;


public class MethodInvocationContext {

  public static void main(){
      System.out.println(A.callM());
      System.out.println(B.callM());
      System.out.println(sub.BOtherPackage.callM());
      System.out.println(A.callMviaB());
      System.out.println(C.callM());
  }
}
  

