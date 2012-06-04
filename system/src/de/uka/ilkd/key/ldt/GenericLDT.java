package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.GenericLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;

/** Generic data type, which has no predefined theory.
 * It is meant as a basis to implement an additional abstract data type,
 * e.g., binary trees, stacks, etc. in <code>.key</code> files.
 * @author daniel
 *
 */
public final class GenericLDT extends LDT {

    public static final Name NAME = new Name("Generic");

    public GenericLDT(Services services) {
        super(NAME, services);
    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right,
            Services services, ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, Services services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        // TODO Auto-generated method stub
        assert false;
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, Services services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return "atom".equals(f.name().toString());
    }

    @Override
    public Expression translateTerm(Term t, ExtList children) {
        if(t.op() instanceof Function && hasLiteralFunction((Function)t.op())) {
            return GenericLiteral.INSTANCE;
        }
        assert false;
        return null;
    }

    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }

}
