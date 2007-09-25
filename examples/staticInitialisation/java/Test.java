public class Test {

   public static void main(String[] args) {
       FailedStaticInit fsi; 
       try { 
	   fsi = new FailedStaticInit();
       } catch (Error e) {
	   System.out.println("FailedStaticInit initialisation failed.");
       }
       fsi = A.SAVE;
       try {
	   fsi.objectMethod();
       } catch(Error e) {         	 
	   System.out.println("FailedStaticInit should be erroneous");
       }
       System.out.println("objectMethod worked: objectVar = "+fsi.objectVar);
   }
}
