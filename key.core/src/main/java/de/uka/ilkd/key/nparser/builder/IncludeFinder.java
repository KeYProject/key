/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser.builder;

import java.io.File;
import java.net.MalformedURLException;
import java.nio.file.Path;

import de.uka.ilkd.key.nparser.JavaKeYParser;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.util.java.StringUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This visitor finds all includes in the given ASTs. It uses {@link Void} as visitor result type,
 * which is treated as {@code @Nullable} under null-marking and therefore cannot satisfy the
 * {@code @NonNull} bound of {@link AbstractBuilder}'s type parameter; the difference is suppressed
 * with a scoped key.
 *
 * @author weigl
 * @see #getIncludes()
 */
@NullMarked
@SuppressWarnings("nullness:type.argument.type.incompatible")
public class IncludeFinder extends AbstractBuilder<Void> {
    private final Path base;
    private final Includes includes = new Includes();
    private boolean ldt = false;

    public IncludeFinder(Path base) {
        this.base = base;
    }

    @Override
    public @Nullable Void visitOne_include_statement(
            JavaKeYParser.One_include_statementContext ctx) {
        ldt = ctx.INCLUDELDTS() != null;
        mapOf(ctx.one_include());
        return null;
    }

    @Override
    public @Nullable Void visitOne_include(JavaKeYParser.One_includeContext ctx) {
        String value = StringUtil.trim(ctx.getText(), "\"'");
        try {
            addInclude(value);
        } catch (MalformedURLException e) {
            throw new BuildingException(ctx, e);
        }
        return null;
    }

    private void addInclude(String filename) throws MalformedURLException {
        RuleSource source;
        if (!filename.endsWith(".key")) {
            filename += ".key";
        }

        filename = filename.replace('/', File.separatorChar); // Not required for Windows, but
        // whatsoever
        filename = filename.replace('\\', File.separatorChar); // Special handling for Linux
        var path = base.resolve(filename).normalize().toAbsolutePath();

        var url = path.toUri().toURL();
        // url = URI.create(path.toString()).toURL();
        source = RuleSourceFactory.initRuleFile(url);
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
