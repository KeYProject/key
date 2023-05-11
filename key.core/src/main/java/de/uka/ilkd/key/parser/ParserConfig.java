package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;

public class ParserConfig {

    private final Services services;
    private final NamespaceSet nss;


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
}
