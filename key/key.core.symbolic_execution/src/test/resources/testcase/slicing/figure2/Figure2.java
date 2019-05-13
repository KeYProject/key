/* @inproceedings{Sridharan:2007:TS:1250734.1250748,
 * author = {Sridharan, Manu and Fink, Stephen J. and Bodik, Rastislav},
 * title = {Thin Slicing},
 * booktitle = {Proceedings of the 2007 ACM SIGPLAN Conference on Programming Language Design and Implementation},
 * series = {PLDI '07},
 * year = {2007},
 * isbn = {978-1-59593-633-2},
 * location = {San Diego, California, USA},
 * pages = {112--122},
 * numpages = {11},
 * url = {http://doi.acm.org/10.1145/1250734.1250748},
 * doi = {10.1145/1250734.1250748},
 * acmid = {1250748},
 * publisher = {ACM},
 * address = {New York, NY, USA},
 * keywords = {debugging, program understanding, slicing},
 *}
 */ 
public class Figure2 {
   static A x;
   static A z;
   static B y;
   static A w;
   static B v;
   
   public static void main() {
      x = new A();
      z = x;
      y = new B();
      w = x;
      w.f = y;
      if (w == z) {
         v = z.f; // the seed
      }
   }
}

class A {
   public B f;
}

class B {
   
}