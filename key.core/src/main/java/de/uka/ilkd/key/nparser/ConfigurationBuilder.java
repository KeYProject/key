package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.util.LinkedHashMap;

import java.util.ArrayList;

/**
 * @author Alexander Weigl
 * @version 1 (03.04.23)
 * @see KeyAst.ConfigurationFile#asConfiguration()
 */
class ConfigurationBuilder extends KeYParserBaseVisitor<Object> {
    private Configuration root;
    private Configuration section;

    public Configuration getConfiguration() {
        return root;
    }

    @Override
    public Object visitCfile(KeYParser.CfileContext ctx) {
        section = root = new Configuration();
        return null;
    }

    @Override
    public Object visitCsection(KeYParser.CsectionContext ctx) {
        var name = ctx.IDENT().getText();
        section = root.getSection(name, true);
        return null;
    }

    @Override
    public Object visitCkv(KeYParser.CkvContext ctx) {
        var name = ctx.ckey().getText();
        var val = ctx.cvalue().accept(this);
        section.set(name, val);
        return null;
    }

    @Override
    public Object visitCsymbol(KeYParser.CsymbolContext ctx) {
        return ctx.IDENT().getText();
    }

    @Override
    public Object visitCstring(KeYParser.CstringContext ctx) {
        final var text = ctx.getText();
        return text.substring(1, text.length() - 1)
                .replace("\\\"", "\"")
                .replace("\\\\", "\\");
    }

    @Override
    public Object visitCintb(KeYParser.CintbContext ctx) {
        return Integer.parseInt(ctx.getText(), 2);
    }

    @Override
    public Object visitCinth(KeYParser.CinthContext ctx) {
        return Integer.parseInt(ctx.getText(), 16);
    }

    @Override
    public Object visitCintd(KeYParser.CintdContext ctx) {
        return Integer.parseInt(ctx.getText(), 10);
    }

    @Override
    public Object visitCfpf(KeYParser.CfpfContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Object visitCfpd(KeYParser.CfpdContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Object visitCfpr(KeYParser.CfprContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Object visitCbool(KeYParser.CboolContext ctx) {
        return Boolean.parseBoolean(ctx.getText());
    }

    @Override
    public Object visitTable(KeYParser.TableContext ctx) {
        var oldSection = section;
        var table = section = new Configuration(new LinkedHashMap<>());
        for (KeYParser.CkvContext context : ctx.ckv()) {
            context.accept(this);
        }
        section = oldSection;
        return table;
    }

    @Override
    public Object visitList(KeYParser.ListContext ctx) {
        var seq = new ArrayList<>(ctx.children.size());
        for (KeYParser.CvalueContext context : ctx.cvalue()) {
            seq.add(context.accept(this));
        }
        return seq;
    }
}
