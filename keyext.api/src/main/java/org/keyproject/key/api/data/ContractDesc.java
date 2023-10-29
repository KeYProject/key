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
        return new ContractDesc(new KeyIdentifications.ContractId(envId, it.id()),
                it.getName(), it.getDisplayName(), it.getTypeName(),
                it.getHTMLText(services), it.getPlainText(services));
    }
}
