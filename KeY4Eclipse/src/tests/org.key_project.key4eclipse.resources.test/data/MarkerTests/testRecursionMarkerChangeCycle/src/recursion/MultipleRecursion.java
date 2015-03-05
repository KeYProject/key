/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package recursion;


/**
 *
 * @author christoph
 */
public class MultipleRecursion {

   int i = 0;
	
   //@ public normal_behavior requires i>=0 && i<=2; ensures true;
   public void a() {
      if (i>=0) b();
      i--;
   }
   //@ public normal_behavior requires i>=0 && i<=2; ensures true;
   public void b() {
      if (i>=0) a();
      i--;
   }
   //@ public normal_behavior requires i>=0 && i<=2; ensures true;
   public void c() {
      if (i>=0) a();
      i--;
   }
}