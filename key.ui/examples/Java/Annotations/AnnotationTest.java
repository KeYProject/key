import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_PARAMETER, ElementType.TYPE_USE})
@interface Unsound {}

final class AnnotationTest {
  public @Unsound Object o;

  // this goal is not soundly closable, but can be closed using
  // the `unsoundFieldClose` rule defined in `unsound.key`
  
  /*@ requires o != null;
    @ ensures false; */
  public void dummy() { }
}
