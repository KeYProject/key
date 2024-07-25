/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;

import org.key_project.logic.Name;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableSet;

public class ExpressionBuilder extends DefaultBuilder {
    public ExpressionBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    protected ImmutableSet<Modality.RustyModalityKind> opSVHelper(String opName, ImmutableSet<Modality.RustyModalityKind> modalityKinds) {
        if (opName.charAt(0) == '#') {
            return lookupOperatorSV(opName, modalityKinds);
        } else {
            Modality.RustyModalityKind m = Modality.RustyModalityKind.getKind(opName);
            if (m == null) {
                semanticError(null, "Unrecognised operator: " + opName);
            }
            modalityKinds = modalityKinds.add(m);
        }
        return modalityKinds;
    }

    private ImmutableSet<Modality.RustyModalityKind> lookupOperatorSV(String opName,
                                                                     ImmutableSet<Modality.RustyModalityKind> modalityKinds) {
        SchemaVariable sv = schemaVariables().lookup(new Name(opName));
        if (sv instanceof ModalOperatorSV osv) {
            modalityKinds = modalityKinds.union(osv.getModalities());
        } else {
            semanticError(null, "Schema variable " + opName + " not defined.");
        }
        return modalityKinds;
    }
}
