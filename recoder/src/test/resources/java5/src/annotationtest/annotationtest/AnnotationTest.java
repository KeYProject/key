package annotationtest;

public class AnnotationTest {
    public int i;
    public int j;

    public @MarkerAnnotation() void  foo() {
    }

    public @AnnotationType(id = 5) void bar() { }
}
