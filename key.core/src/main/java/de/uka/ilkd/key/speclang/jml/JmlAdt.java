package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.SpecificationElement;
import org.jspecify.annotations.Nullable;

import java.util.function.UnaryOperator;

/**
 * @author Alexander Weigl
 * @version 1 (27.02.25)
 */
public class JmlAdt implements SpecificationElement {
    @Override
    public String getName() {
        return "";
    }

    @Override
    public String getDisplayName() {
        return "";
    }

    @Override
    public @Nullable VisibilityModifier getVisibility() {
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
        return null;
    }

    @Override
    public SpecificationElement map(UnaryOperator<Term> op, Services services) {
        return null;
    }
}
