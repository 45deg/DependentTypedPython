"""Sphinx directive for DepPy sources that must not be imported as Python."""

import ast
from pathlib import Path

from docutils import nodes
from docutils.statemachine import StringList
from sphinx.util.docutils import SphinxDirective


class DepPyApi(SphinxDirective):
    """Render signatures and docstrings from a DepPy source file via ``ast``."""

    required_arguments = 1
    has_content = False

    def run(self):
        source = Path(self.env.srcdir).parent / self.arguments[0]
        self.env.note_dependency(str(source))
        source_text = source.read_text(encoding="utf-8")
        tree = ast.parse(source_text, filename=str(source))
        result = []
        for item in tree.body:
            if not isinstance(item, (ast.ClassDef, ast.FunctionDef)):
                continue
            doc = ast.get_docstring(item, clean=True)
            if not doc:
                continue
            kind = "class" if isinstance(item, ast.ClassDef) else "function"
            section = nodes.section(ids=[f"{source.stem}-{item.name}"])
            section += nodes.title(text=f"{item.name} ({kind})")
            signature = ast.get_source_segment(source_text, item)
            first_line = signature.splitlines()[0] if signature else item.name
            section += nodes.literal_block(text=first_line.rstrip(":"))
            container = nodes.container()
            self.state.nested_parse(StringList(doc.splitlines(), source=str(source)), self.content_offset, container)
            section.extend(container.children)
            result.append(section)
        return result


def setup(app):
    app.add_directive("deppy-api", DepPyApi)
    return {"version": "1.0", "parallel_read_safe": True}
