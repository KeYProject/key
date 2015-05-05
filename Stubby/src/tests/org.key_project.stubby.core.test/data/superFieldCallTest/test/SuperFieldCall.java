public class SuperFieldCall {
   int integerfieldA;
}

class SuperFieldB extends SuperFieldCall{
   protected int integerfieldA;
  
   void superFieldBAccess(){
      super.integerfieldA = this.integerfieldA;
   }
}