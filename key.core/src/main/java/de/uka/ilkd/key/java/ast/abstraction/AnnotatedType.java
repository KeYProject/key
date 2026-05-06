package de.uka.ilkd.key.java.ast.abstraction;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ast.expression.AnnotationExpression;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;

public class AnnotatedType implements Type {
    private Type subType;
    private ImmutableArray<AnnotationExpression> annotations;

    public AnnotatedType(Type subType, 
            ImmutableArray<AnnotationExpression> annotations) {
        assert subType.getAnnotations().size() == 0;
        this.subType = subType;
        this.annotations = annotations;
    }

    @Override
    public String getFullName() {
        return subType.getFullName();
    }

    @Override
    public String getName() {
        return subType.getName();
    }

    @Override
    public Literal getDefaultValue() {
        return subType.getDefaultValue();
    }

    @Override
    public ImmutableArray<AnnotationExpression> getAnnotations() {
        return annotations;
    }
}
