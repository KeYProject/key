/* 
 * looks a bit similar to Throwable in javaRedux
 * added to test !399 (parsing of @set annotations in method/constructor)
 *
 */

public class SetInMethodBody
{

   //@ protected nullable ghost String message = null;
   //@ protected nullable ghost Throwable cause = null;

   
   /*@ public normal_behavior
     @    requires true;
     @    ensures message == arg0 && cause == arg1;
     @    assignable message, cause;
     @*/
   public void foo(java.lang.String arg0, java.lang.Throwable arg1) {
       // this is what we want to parse:
       //@ set message = arg0;
       // some random comment to make things harder
       //@ set cause = arg1;
       // another random comment
   }
   
}
