public class NestedFieldCallTest {
   int intField;
   NestedFieldCallTest next;
   
   public void callStringField(){
      next.next.intField = 42;
   }
}
