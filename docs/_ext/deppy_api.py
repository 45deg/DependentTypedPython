"""Static Sphinx reference for checked DepPy declarations."""

import ast
from pathlib import Path
import textwrap

from docutils import nodes
from docutils.parsers.rst import directives
from docutils.statemachine import StringList
from sphinx.errors import SphinxError
from sphinx.util.docutils import SphinxDirective


def signature(source_text, item):
    """Return the complete source header, including multiline type parameters."""
    lines = source_text.splitlines()
    first_body = item.body[0]
    body_prefix = lines[first_body.lineno - 1][:first_body.col_offset]
    if body_prefix.rstrip().endswith(":"):
        header_lines = lines[item.lineno - 1:first_body.lineno]
        header_lines[-1] = body_prefix
    else:
        header_lines = lines[item.lineno - 1:first_body.lineno - 1]
    header = "\n".join(header_lines).rstrip()
    return header


def declaration(source_text, item):
    header = signature(source_text, item)
    if isinstance(item, ast.FunctionDef):
        return header
    parts = [header]
    for child in item.body:
        if isinstance(child, ast.AnnAssign):
            parts.append("    " + ast.get_source_segment(source_text, child).strip())
        elif isinstance(child, ast.FunctionDef):
            parts.append(textwrap.indent(textwrap.dedent(signature(source_text, child)), "    "))
    return "\n".join(parts)


class DepPyApi(SphinxDirective):
    """Render a selected source API without executing checked Python."""

    required_arguments = 1
    has_content = False
    option_spec = {"members": directives.unchanged}

    def run(self):
        source = Path(self.env.srcdir).parent / self.arguments[0]
        self.env.note_dependency(str(source))
        source_text = source.read_text(encoding="utf-8")
        tree = ast.parse(source_text, filename=str(source))
        local = {item.name: item for item in tree.body if isinstance(item, (ast.ClassDef, ast.FunctionDef))}
        selected = self.options.get("members")
        if selected is None:
            names = [name for name, item in local.items() if ast.get_docstring(item)]
        else:
            names = [name.strip() for name in selected.replace("\n", " ").split(",") if name.strip()]
            if not names or len(set(names)) != len(names):
                raise SphinxError(f"Invalid or repeated :members: in {source}")

        builtin_imports = {
            alias.asname or alias.name: alias.name
            for item in tree.body
            if isinstance(item, ast.ImportFrom) and item.module == "deppy._builtins"
            for alias in item.names
        }
        builtin_source = source.parent / "_builtins.py"
        builtin_text = builtin_source.read_text(encoding="utf-8") if builtin_source.exists() else ""
        builtin_tree = ast.parse(builtin_text, filename=str(builtin_source))
        builtins = {item.name: item for item in builtin_tree.body if isinstance(item, (ast.ClassDef, ast.FunctionDef))}

        result = []
        for name in names:
            item = local.get(name)
            from_builtin = item is None and name in builtin_imports
            if from_builtin:
                item = builtins.get(builtin_imports[name])
                self.env.note_dependency(str(builtin_source))
            if item is None:
                raise SphinxError(f"Selected deppy-api member {name!r} has no declaration in {source}")
            doc = ast.get_docstring(item, clean=True)
            builtin_declaration = any(
                isinstance(decorator, ast.Name) and decorator.id == "builtin"
                for decorator in item.decorator_list
            )
            if selected is not None and not doc and not builtin_declaration:
                raise SphinxError(f"Selected deppy-api member {name!r} has no docstring in {source}")
            kind = "class" if isinstance(item, ast.ClassDef) else "function"
            qualified = f"deppy.{source.stem}.{name}"
            label = qualified.lower()
            if name != name.lower() and any(other != name and other.lower() == name.lower() for other in names):
                label += "-constructor"
            target = nodes.target(names=[label], ids=[qualified])
            self.state.document.note_explicit_target(target)
            section = nodes.section(ids=[qualified + "-detail"])
            section += nodes.title(text=f"{name} ({kind})")
            section += nodes.literal_block(text=declaration(builtin_text if from_builtin else source_text, item))
            if isinstance(item, ast.ClassDef):
                for child in item.body:
                    if isinstance(child, ast.FunctionDef):
                        child_name = f"deppy.{source.stem}.{child.name}"
                        child_target = nodes.target(names=[child_name.lower() + "-constructor"], ids=[child_name])
                        self.state.document.note_explicit_target(child_target)
                        section += child_target
            if doc:
                container = nodes.container()
                self.state.nested_parse(StringList(doc.splitlines(), source=str(source)), self.content_offset, container)
                section.extend(container.children)
            result.extend([target, section])
        return result


def setup(app):
    app.add_directive("deppy-api", DepPyApi)
    return {"version": "2.0", "parallel_read_safe": True}
