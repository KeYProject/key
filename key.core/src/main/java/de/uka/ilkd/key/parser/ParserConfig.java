/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYRecoderMapping;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.NamespaceSet;

public class ParserConfig {

    private Services services;
    private NamespaceSet nss;


    public ParserConfig(Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }


    public Services services() {
        return services;
    }

    public NamespaceSet namespaces() {
        return nss;
    }

    public JavaInfo javaInfo() {
        return services.getJavaInfo();
    }

    public KeYRecoderMapping keyRecoderMapping() {
        return services.getJavaInfo().rec2key();
    }

    public TypeConverter typeConverter() {
        return services.getTypeConverter();
    }

    public KeYCrossReferenceServiceConfiguration serviceConfiguration() {
        return services.getJavaInfo().getKeYProgModelInfo().getServConf();
    }

}
