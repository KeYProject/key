package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.pp.Layouter;


/**
 * A schema variable that is used as placeholder for updates.
 */
public final class UpdateSV extends AbstractSV {


    UpdateSV(Name name) {
        super(name, Sort.UPDATE, false, true);
    }


    @Override
    public String toString() {
        return toString("update");
    }

    @Override
    public void layout(Layouter<?> l) {
        l.print("\\schemaVar \\update ").print(name().toString());
    }
}
