
public class UpdateVariablesTest {
   public static int classUnused;
   public static int classRead;
   public static int classWrite;

   public int fieldUnused;
   public int fieldRead;
   public int fieldWrite;
   
   public int main() {
      classWrite = classRead;
      fieldWrite = fieldRead;
      return classWrite + fieldWrite;
   }
}
