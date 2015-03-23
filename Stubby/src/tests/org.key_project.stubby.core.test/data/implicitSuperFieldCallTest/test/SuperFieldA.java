public class SuperFieldA {
   int integerfieldA;
}

class SuperFieldB extends SuperFieldA{
   void superFieldBAccess(){
      integerfieldA = 42;
   }
//   SuperFieldA(){
//      integerfieldA = 12;
//   }
}