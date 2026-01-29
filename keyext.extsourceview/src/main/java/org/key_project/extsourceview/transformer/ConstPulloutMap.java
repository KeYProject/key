package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.Pair;

import java.util.Map;
import java.util.Set;

public class ConstPulloutMap {
    private final Map<String, Pair<PosInOccurrence, JTerm>> replMap;
    private final Set<JTerm> constExtrSet;

    public ConstPulloutMap(Map<String, Pair<PosInOccurrence, JTerm>> replMap, Set<JTerm> constExtrSet) {
        this.replMap = replMap;
        this.constExtrSet = constExtrSet;
    }

    public boolean containsFormula(PosInOccurrence pio) {
        return constExtrSet.contains(pio.subTerm());
    }

    public @Nullable JTerm replace(TermFactory tf, JTerm term) {
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

    public PosInOccurrence getPIO(JTerm term) {
        return replMap.get(term.op().name().toString()).first;
    }
}
