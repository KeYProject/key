/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;

import org.key_project.rusty.parser.KeYRustyParser;
import org.key_project.rusty.proof.init.Includes;
import org.key_project.rusty.proof.io.RuleSource;
import org.key_project.rusty.proof.io.RuleSourceFactory;
import org.key_project.rusty.util.parsing.BuildingException;
import org.key_project.util.java.StringUtil;

public class IncludeFinder extends AbstractBuilder<Void> {
    private final URL base;
    private final Includes includes = new Includes();
    private final String basePath;
    private boolean ldt = false;

    public IncludeFinder(URL base) {
        this.base = base;
        String a = base.getPath();
        basePath = a.substring(0, a.lastIndexOf('/'));
    }

    @Override
    public Void visitOne_include_statement(KeYRustyParser.One_include_statementContext ctx) {
        ldt = ctx.INCLUDELDTS() != null;
        mapOf(ctx.one_include());
        return null;
    }

    @Override
    public Void visitOne_include(KeYRustyParser.One_includeContext ctx) {
        String value = StringUtil.trim(ctx.getText(), "\"'");
        try {
            addInclude(value, ctx.relfile != null);
        } catch (MalformedURLException e) {
            throw new BuildingException(ctx, e);
        }
        return null;
    }

    private void addInclude(String filename, boolean relativePath) throws MalformedURLException {
        RuleSource source;
        if (!filename.endsWith(".key")) {
            filename += ".key";
        }

        if (relativePath) {
            filename = filename.replace('/', File.separatorChar); // Not required for Windows, but
            // whatsoever
            filename = filename.replace('\\', File.separatorChar); // Special handling for Linux
            URL path = new URL(base.getProtocol(), base.getHost(), base.getPort(),
                basePath + "/" + filename);
            source = RuleSourceFactory.initRuleFile(path);
        } else {
            source = RuleSourceFactory.fromDefaultLocation(filename);
        }
        if (ldt) {
            includes.putLDT(filename, source);
        } else {
            includes.put(filename, source);
        }
    }

    public Includes getIncludes() {
        return includes;
    }
}
