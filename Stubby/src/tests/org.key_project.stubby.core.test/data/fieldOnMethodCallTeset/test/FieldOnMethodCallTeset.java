
public class FieldOnMethodCallTeset {
   private int value;
   
   public int main() {
      return next().value;
   }
   
   public FieldOnMethodCallTeset next() {
      return this;
   }
}
