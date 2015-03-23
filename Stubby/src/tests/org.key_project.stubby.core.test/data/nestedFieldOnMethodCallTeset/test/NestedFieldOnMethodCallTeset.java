
public class NestedFieldOnMethodCallTeset {
   private int value;
   
   public int main() {
      return next().anotherNext().value;
   }
   
   public NestedFieldOnMethodCallTeset next() {
      return this;
   }
   
   public NestedFieldOnMethodCallTeset anotherNext() {
      return this;
   }
}
