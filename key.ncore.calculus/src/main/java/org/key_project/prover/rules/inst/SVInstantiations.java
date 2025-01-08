/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.inst;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;

public interface SVInstantiations {

    public SchemaVariable lookupVar(Name name);

    public Object lookupValue(Name name);

    public Object getInstantiation(SchemaVariable sv);

    boolean isInstantiated(SchemaVariable sv);

    SVInstantiations union(SVInstantiations instantiations, LogicServices services);
}
