/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;

import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;

/**
 * The file-backed library of user-defined skills (Markdown files with a YAML front matter in the
 * KeY config directory). An active skill is selected on the {@link LlmSession}; its instructions
 * are appended to the system prompt and its {@code allowedTools} whitelist narrows the advertised
 * tool set.
 * <p>
 * The library is <em>seeded</em>: when the skill search path is empty (only the default directory
 * {@link #defaultDir()} is searched) and that directory has no {@code .md} files yet, the skills
 * bundled with KeY (the classpath resource {@code /skills.zip}, built from the repository
 * directory {@code keyext.llm/skills}) are extracted into it. Deleting a seeded skill removes it
 * for good.
 *
 * @author Alexander Weigl
 */
public final class SkillLibrary extends FileBackedLibrary<Skill> {
    public static final SkillLibrary INSTANCE = new SkillLibrary();

    /** The classpath resource holding the shipped skills ({@code <name>.md} entries). */
    public static final String SHIPPED_SKILLS_RESOURCE = "/skills.zip";

    private SkillLibrary() {
    }

    // ------------------------------------------------------------- FileBackedLibrary hooks

    @Override
    protected String subDirectory() {
        return "skills";
    }

    @Override
    protected void seedDefaultDirectory(Path dir) throws IOException {
        if (hasMarkdownFiles(dir)) {
            return; // the user already has skills there
        }
        var entries = readShippedSkills();
        if (entries.isEmpty()) {
            return;
        }
        Files.createDirectories(dir);
        for (var entry : entries.entrySet()) {
            // plain file names only, defending against archive paths
            var file = dir.resolve(Path.of(entry.getKey()).getFileName());
            Files.writeString(file, entry.getValue(), StandardCharsets.UTF_8);
        }
    }

    /** True when {@code dir} already holds {@code .md} files (so no seeding is needed). */
    private static boolean hasMarkdownFiles(Path dir) throws IOException {
        if (!Files.isDirectory(dir)) {
            return false;
        }
        try (var stream = Files.list(dir)) {
            return stream.anyMatch(p -> p.toString().toLowerCase(Locale.ROOT).endsWith(".md"));
        }
    }

    /** The shipped skills as archive-path -&gt; Markdown content; empty when not bundled. */
    static LinkedHashMap<String, String> readShippedSkills() {
        try (InputStream in = SkillLibrary.class.getResourceAsStream(SHIPPED_SKILLS_RESOURCE)) {
            if (in == null) {
                return new LinkedHashMap<>();
            }
            var entries = new LinkedHashMap<String, String>();
            LibraryZip.read(in).forEach((name, content) -> {
                if (name.endsWith(".md")) {
                    entries.put(name, content);
                }
            });
            return entries;
        } catch (IOException e) {
            return new LinkedHashMap<>();
        }
    }

    @Override
    protected List<String> configuredSearchPath() {
        return LlmSettings.INSTANCE.getSkillLibraryPaths();
    }

    @Override
    protected @Nullable Skill fromMarkdown(String markdown) {
        return parse(markdown);
    }

    @Override
    protected String toMarkdown(Skill element) {
        return serialize(element);
    }

    @Override
    protected @Nullable Skill fromLegacyJson(String json) {
        try {
            return new GsonBuilder().create().fromJson(json, Skill.class);
        } catch (Exception e) {
            return null;
        }
    }

    @Override
    protected String nameOf(Skill element) {
        return element.name();
    }

    @Override
    protected String validate(Skill element) {
        if (!validName(element.name())) {
            return "Name may only contain letters, digits, '_' and '-'.";
        }
        return null;
    }

    // ------------------------------------------------- public Markdown format (used by the editor)

    /**
     * Parses a skill from its Markdown document (YAML front matter: {@code name},
     * {@code description}, {@code enabled}, optional {@code allowedTools}; body: the
     * instructions). Returns {@code null} when the document has no usable front matter or a blank
     * name.
     */
    public static @Nullable Skill parse(String markdown) {
        var parsed = MarkdownFrontMatter.parse(markdown);
        if (parsed == null) {
            return null;
        }
        var meta = parsed.meta();
        var name = MarkdownFrontMatter.stringValue(meta, "name");
        if (name == null || name.isBlank()) {
            return null;
        }
        var description = MarkdownFrontMatter.stringValue(meta, "description");
        boolean enabled = meta.get("enabled") instanceof Boolean b ? b : true;
        var allowedTools = MarkdownFrontMatter.stringList(meta, "allowedTools");
        return new Skill(name, description, parsed.body(), allowedTools, enabled);
    }

    /** Serializes a skill to its Markdown document. */
    public static String serialize(Skill skill) {
        var meta = new LinkedHashMap<String, Object>();
        meta.put("name", skill.name());
        meta.put("description", skill.description());
        meta.put("enabled", skill.enabled());
        if (!skill.allowedTools().isEmpty()) {
            meta.put("allowedTools", skill.allowedTools());
        }
        return MarkdownFrontMatter.render(meta, skill.instructions());
    }
}
