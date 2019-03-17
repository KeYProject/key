
public class ExistsQuantifierTest {
   /*@
     @ invariant (\exists ExistsQuantifierTest p; p.id == this.id ==> p == this);
     @*/
   private /*@ spec_public @*/ int id;
   
   /*@ normal_behavior
     @ ensures true;
     @*/
   public void compute() {
   }
}
