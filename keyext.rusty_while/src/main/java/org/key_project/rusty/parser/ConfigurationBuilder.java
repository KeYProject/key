/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.stream.Collectors;

import org.key_project.rusty.settings.Configuration;

import org.jspecify.annotations.NonNull;

public class ConfigurationBuilder extends KeYRustyParserBaseVisitor<Object> {
    @Override
    public List<Object> visitCfile(KeYRustyParser.CfileContext ctx) {
        return ctx.cvalue().stream().map(it -> it.accept(this)).collect(Collectors.toList());
    }

    @Override
    public String visitCkey(KeYRustyParser.CkeyContext ctx) {
        if (ctx.STRING_LITERAL() != null)
            return sanitizeStringLiteral(ctx.STRING_LITERAL().getText());
        return ctx.IDENT().getText();
    }

    @Override
    public String visitCsymbol(KeYRustyParser.CsymbolContext ctx) {
        return ctx.IDENT().getText();
    }


    @Override
    public String visitCstring(KeYRustyParser.CstringContext ctx) {
        final var text = ctx.getText();
        return sanitizeStringLiteral(text);
    }

    private static @NonNull String sanitizeStringLiteral(String text) {
        return text.substring(1, text.length() - 1)
                .replace("\\\"", "\"")
                .replace("\\\\", "\\");
    }

    @Override
    public Long visitCintb(KeYRustyParser.CintbContext ctx) {
        return Long.parseLong(ctx.getText(), 2);
    }

    @Override
    public Long visitCinth(KeYRustyParser.CinthContext ctx) {
        return Long.parseLong(ctx.getText(), 16);
    }

    @Override
    public Long visitCintd(KeYRustyParser.CintdContext ctx) {
        final var text = ctx.getText();
        if (text.endsWith("L") || text.endsWith("l")) {
            return Long.parseLong(text.substring(0, text.length() - 1), 10);
        } else {
            return Long.parseLong(text, 10);
        }
    }

    @Override
    public Double visitCfpf(KeYRustyParser.CfpfContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Double visitCfpd(KeYRustyParser.CfpdContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Double visitCfpr(KeYRustyParser.CfprContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Boolean visitCbool(KeYRustyParser.CboolContext ctx) {
        return Boolean.parseBoolean(ctx.getText());
    }

    @Override
    public Configuration visitTable(KeYRustyParser.TableContext ctx) {
        final var data = new LinkedHashMap<String, Object>();
        for (KeYRustyParser.CkvContext context : ctx.ckv()) {
            var name = context.ckey().accept(this).toString();
            var val = context.cvalue().accept(this);
            data.put(name, val);
        }
        return new Configuration(data);
    }

    @Override
    public List<Object> visitList(KeYRustyParser.ListContext ctx) {
        var seq = new ArrayList<>(ctx.children.size());
        for (KeYRustyParser.CvalueContext context : ctx.cvalue()) {
            seq.add(context.accept(this));
        }
        return seq;
    }
}
