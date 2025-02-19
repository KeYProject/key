/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record ContractDesc(KeyIdentifications.ContractId contractId, String name, String displayName,
                           String typeName, String htmlText, String plainText) {
    public static ContractDesc from(KeyIdentifications.EnvironmentId envId, Services services, Contract it) {
        return new ContractDesc(new KeyIdentifications.ContractId(envId, it.getName()),
                it.getName(), it.getDisplayName(), it.getTypeName(),
                it.getHTMLText(services), it.getPlainText(services));
    }
}
