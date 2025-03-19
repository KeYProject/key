package annotationtest;

public @interface AnnotationType {
    int id() default -1;
    
    final int someValue = 0;
}

class Test implements AnnotationType {
    public int id() { return 0; }
    public Class annotationType() { return null; }

}

@AnnotationType class  B { }
