package de.uka.ilkd.key.logic;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public class TermCreationException extends RuntimeException {

    /**
     * generated serial version UID
     */
    private static final long serialVersionUID = -7173044450561438150L;

    public TermCreationException(String errorMessage) {
        super(errorMessage);
    }

    public TermCreationException(Operator op, Term failed) {
        super(getErrorMessage(op, failed));
    }

    private static String getErrorMessage(Operator op, Term failed) {
        ImmutableArray<Term> subs = failed.subs();
        for (int i = 0, n = subs.size(); i < n; i++) {
            Term sub = subs.get(i);
            assert sub == failed.subs().get(i);
        }

        return "Building a term failed. Normally there is an arity mismatch "
            + "or one of the subterms' sorts "
            + "is not compatible (e.g. like the \'2\' in \"true & 2\")\n"
            + "The top level operator was " + op + "(Sort: " + op.sort(subs) + ")"
            + (op instanceof SortedOperator
                    ? "; its expected arg sorts were:\n" + argsToString((SortedOperator) op)
                    : "")
            + "\nThe subterms were:\n" + subsToString(subs);
    }

    private static String argsToString(SortedOperator f) {
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < f.arity(); i++) {
            sb.append((i + 1) + ".) ");
            sb.append("sort: " + f.argSort(i)
                + (f.argSort(i) == null ? "" : ", sort hash: " + f.argSort(i).hashCode()) + "\n");
        }
        return sb.toString();
    }

    private static String subsToString(ImmutableArray<Term> subs) {
        StringBuffer sb = new StringBuffer();
        for (int i = 0, n = subs.size(); i < n; i++) {
            sb.append((i + 1) + ".) ");
            Term subi = subs.get(i);
            if (subi != null) {
                sb.append(subi);
                Sort subiSort = subi.sort();
                if (subiSort != null) {
                    sb.append(
                        "(sort: " + subi.sort() + ", sort hash: " + subi.sort().hashCode() + ")\n");
                } else {
                    sb.append("(Unknown sort, \"null pointer\")");
                }
            } else {
                sb.append(" !null!\n");
            }

        }
        return sb.toString();
    }
}
