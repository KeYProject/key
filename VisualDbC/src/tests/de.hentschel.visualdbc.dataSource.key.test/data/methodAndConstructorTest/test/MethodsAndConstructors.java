import java.util.Collection;


public abstract class MethodsAndConstructors extends MethodsAndConstructorsParent {
   public MethodsAndConstructors() {
   }

   public MethodsAndConstructors(MyClass c) {
   }

   private MethodsAndConstructors(int i) {
   }

   protected MethodsAndConstructors(String j) {
   }

   MethodsAndConstructors(int i, String j) {
   }
   
   public void doSomething() {
   }
   
   public int doSomething(int i) {
      return 0;
   }
   
   private String doSomethingElse(int[] i) {
      return null;
   }
   
   private String doSomethingElse(int[][] i) {
      return null;
   }
   
   protected String[] doSomethingArray(String[] sArray, MyClass[] myArray, boolean[] boolArray) {
	   return null;
   }
   
// Not supported by KeY??
//   public <T> T doCollection(T t) {
//	   return null;
//   }
   
// Not correctly supported by KeY??
//   public void doEndlesParameter(String... x) {
//   }
   
   double doSomethingElse(int i, MyClass c) {
      return 0.0;
   }
   
   static double doStatic(int i, MyClass c) {
      return 0.0;
   }
   
   public static final void doStatic(String x) {
   }
   
   protected abstract MyClass doAbstract(String x);
}