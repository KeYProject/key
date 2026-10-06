public class AnnDecl {
    @interface Marker { int value() default 0; }
    @Marker(3) int x;
}
