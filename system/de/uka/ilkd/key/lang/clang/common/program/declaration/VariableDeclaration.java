package de.uka.ilkd.key.lang.clang.common.program.declaration;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangTerminalProgramElement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.util.ExtList;

public final class VariableDeclaration extends BaseClangStatement {
        private IClangTypeReference typeReference;

        private IClangVariable variable;

        private IClangExpression initializer;

        private boolean isStatic;

        public static class Modifier extends BaseClangTerminalProgramElement
                        implements IProgramElement {
                private final String name;

                private Modifier(String name) {
                        this.name = name;
                }

                public String getModifierName() {
                        return name;
                }

                public boolean equalsModRenaming(IProgramElement pe,
                                NameAbstractionTable nat) {
                        return pe == this;
                }

                public void dispatch(IClangProgramDispatcher p)
                                throws java.lang.Exception {
                        p.dispatchModifier(this);
                }

                public final static Modifier STATIC = new Modifier("static");
        }

        public VariableDeclaration(IClangTypeReference typeReference,
                        IClangVariable variable, IClangExpression initializer,
                        boolean isStatic) {
                this.typeReference = typeReference;
                this.variable = variable;
                this.initializer = initializer;
                this.isStatic = isStatic;
        }

        public VariableDeclaration(ExtList children,
                        VariableDeclaration original) {
                super(children);
                this.typeReference = (IClangTypeReference) children
                                .get(IClangTypeReference.class);
                this.variable = (IClangVariable) children
                                .get(IClangVariable.class);
                IClangExpression[] expressions = (IClangExpression[]) children
                                .collect(IClangExpression.class);
                this.initializer = expressions.length == 2 ? expressions[1]
                                : null;
                this.isStatic = original.isStatic;
        }
        
        public IProgramElement copy(ExtList children) {
                return new VariableDeclaration(children, this);
        }
        
        public boolean getIsStatic() {
                return isStatic;
        }

        public IClangTypeReference getTypeReference() {
                return typeReference;
        }

        public IClangVariable getVariable() {
                return variable;
        }

        public IClangExpression getInitializer() {
                return initializer;
        }

        public int getChildCount() {
                return (isStatic ? 1 : 0) + 2 + (initializer != null ? 1 : 0);
        }

        public IProgramElement getProgramElementAt(int index) {
                if (isStatic) {
                        if (index == 0)
                                return Modifier.STATIC;
                        else
                                index--;
                }
                if (index == 0)
                        return typeReference;
                else if (index == 1)
                        return variable;
                else if (index == 2 && initializer != null)
                        return initializer;
                else
                        throw new ArrayIndexOutOfBoundsException();
        }

        public boolean equalsModRenaming(IProgramElement pe,
                        NameAbstractionTable nat) {
                if (!(pe instanceof VariableDeclaration))
                        return false;
                final VariableDeclaration variableDeclaration = (VariableDeclaration) pe;
                
                // Declared variable inequality does not matter
                nat.add(variable, variableDeclaration.getVariable());
                
                return super.equalsModRenaming(pe, nat);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchVariableDeclaration(this);
        }
}
