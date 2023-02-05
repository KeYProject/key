package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.Pair;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

public class ConstPulloutMap {
    private final Map<String, Pair<PosInOccurrence, Term>> replMap;
    private final Set<Term> constExtrSet;

    public ConstPulloutMap(Map<String, Pair<PosInOccurrence, Term>> replMap, Set<Term> constExtrSet) {
        this.replMap = replMap;
        this.constExtrSet = constExtrSet;
    }

    public boolean containsFormula(PosInOccurrence pio) {
        return constExtrSet.contains(pio.subTerm());
    }

    public @Nullable Term replace(TermFactory tf, Term term) {
        if (term.arity() != 0) return null;
        var repl = replMap.get(term.op().name().toString());
        if (repl == null) return null;
        if (!(term.op() instanceof Function)) return null;

        var replTerm = repl.second;

        if (!term.getOriginRef().isEmpty()) {
            replTerm = tf.addOriginRef(replTerm, term.getOriginRef());
        }

        return replTerm;
    }

    public PosInOccurrence getPIO(Term term) {
        return replMap.get(term.op().name().toString()).first;
    }
}
