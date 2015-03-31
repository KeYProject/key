import java.util.Comparator;

public final class ObjectUtil {
   public static <T> Comparator<T> createEqualsComparator() {
       return new Comparator<T>() {
           @Override
           public int compare(T arg0, T arg1) {
               return 0;
           }
       };
   }
}