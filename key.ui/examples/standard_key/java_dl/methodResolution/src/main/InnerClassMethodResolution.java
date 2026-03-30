package main;

public class InnerClassMethodResolution {
    public static void main(){
        System.out.println(Outer.callM());
        System.out.println(Outer.B.callM());
        System.out.println(Outer.callMviaB());
    }
}
