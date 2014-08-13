
public class GlobalAccessesAndModifications {

   public int access;
   
   public int modification;
   
   public int accessAndModification;
   
   public void main(){
      for(int i = 0; i<2; i++){
         doAccessesAndModifications();
      }
   }
   
   public void doAccessesAndModifications(){
      modification=5;
      
      int x = access;
      
      x = someAccessMethod(access);
      
      x = someInternalAccessMethod(access).doNothing();
      
      accessAndModification=accessAndModification;
      
      accessAndModification = someAccessMethod(accessAndModification);
      
      accessAndModification = someInternalAccessMethod(accessAndModification).doNothing();
   }
   
   public int someAccessMethod(int access){
      return 5;
   }
   
   public GlobalAccessesAndModifications someInternalAccessMethod(int x){
      return new GlobalAccessesAndModifications();
   }
   
   public int doNothing(){
      return 5;
   }
}
