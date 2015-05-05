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
      i--;
   }
   //@ public normal_behavior requires i>=0 && i<=2; ensures true;
   public void b() {
      i--;
   }
}