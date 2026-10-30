#!/usr/bin/env python3
"""Render the package's statement and verification guide."""
import json
from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak,
)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'PDF/fujita-freeness-guide.pdf'
OUT.parent.mkdir(exist_ok=True)
pdfmetrics.registerFont(TTFont('Guide', '/System/Library/Fonts/Supplemental/Arial.ttf'))
pdfmetrics.registerFont(TTFont('GuideMath', '/System/Library/Fonts/Supplemental/Arial Unicode.ttf'))
pdfmetrics.registerFont(TTFont('GuideBold', '/System/Library/Fonts/Supplemental/Arial Bold.ttf'))
pdfmetrics.registerFontFamily('Guide', normal='Guide', bold='GuideBold', italic='Guide', boldItalic='GuideBold')
ink, teal, muted = colors.HexColor('#183239'), colors.HexColor('#176b60'), colors.HexColor('#53666a')
styles = getSampleStyleSheet()
styles.add(ParagraphStyle(name='TitleCustom', fontName='GuideBold', fontSize=24, leading=30, textColor=ink, spaceAfter=10))
styles.add(ParagraphStyle(name='LeadCustom', fontName='Guide', fontSize=10.5, leading=15.5, textColor=muted, spaceAfter=13))
styles.add(ParagraphStyle(name='HeadingCustom', fontName='GuideBold', fontSize=12, leading=17, textColor=teal, spaceBefore=14, spaceAfter=7))
styles.add(ParagraphStyle(name='BodyCustom', fontName='Guide', fontSize=10, leading=15, textColor=ink, spaceAfter=8))
styles.add(ParagraphStyle(name='SmallCustom', fontName='Guide', fontSize=8.5, leading=12.5, textColor=muted, spaceAfter=5))
styles.add(ParagraphStyle(name='MathCustom', fontName='GuideMath', fontSize=14, leading=23, textColor=ink, alignment=TA_CENTER, spaceBefore=9, spaceAfter=12))


def p(text, style='BodyCustom'):
    return Paragraph(text, styles[style])


def footer(canvas, doc):
    canvas.saveState()
    canvas.setStrokeColor(colors.HexColor('#d5dfdb'))
    canvas.line(20*mm, 17*mm, 190*mm, 17*mm)
    canvas.setFont('Guide', 8)
    canvas.setFillColor(muted)
    canvas.drawString(20*mm, 12*mm, 'Fujita freeness | Local package | 23 October 2026')
    canvas.drawRightString(190*mm, 12*mm, str(doc.page))
    canvas.restoreState()


story = [p('Fujita freeness<br/>and its mixed variant', 'TitleCustom'),
         p('Statements, proof route and verification guide', 'LeadCustom')]
story += [p('1. The classical problem', 'HeadingCustom'),
          p('Let X be a smooth complex projective variety of dimension n &ge; 1, and let L be an ample Cartier divisor. Fujita\'s freeness conjecture asks for:'),
          p('K<sub>X</sub> + mL is globally generated for every integer m &ge; n + 1.', 'MathCustom'),
          p('Global generation means that every point admits a global section that does not vanish there. This package concerns freeness, rather than the separate very-ampleness conjecture.'),
          p('2. The mixed variant (F1)', 'HeadingCustom'),
          p('Let L<sub>1</sub>, ..., L<sub>s</sub> be ample Cartier divisors, with s &ge; n + 1, and let N be nef Cartier. The mixed statement asks for:'),
          p('K<sub>X</sub> + L<sub>1</sub> + ... + L<sub>s</sub> + N is globally generated.', 'MathCustom'),
          p('<b>Mixed implies classical.</b> Put s = m, take every L<sub>i</sub> = L and N = 0. The solution entry proves this specialization in Lean. The extra nef summand can also be absorbed into the first ample divisor.'),
          p('3. Sources and attribution', 'HeadingCustom')]
for name, text in [
    ('Fujita (1987)', 'Original source of the classical conjecture. DOI: 10.2969/aspm/01010167.'),
    ('Chen-Kuronya-Mustopa-Stix (2024)', 'Section 1.2 states the mixed problem through convex Fujita numbers. arXiv:2301.06367v2.'),
    ('OpenAI (2026)', 'The Fujita manuscript claims a proof of the classical case. Its minimization and center-exclusion strategy informed this development. It is not the original source of the mixed problem.'),
]:
    story.append(p('<b>'+name+'.</b> '+text))
story.append(p('The OpenAI catalogue checked on 23 October 2026 did not list a Lean proof for that Fujita manuscript. Adapted OpenAI sources for other foundational results are identified separately in vendor/provenance.json.', 'SmallCustom'))
story += [PageBreak(), p('Proof and verification', 'TitleCustom'),
          p('Library-backed proofs and a separate proposed FC statement', 'LeadCustom'),
          p('4. Proof route', 'HeadingCustom'),
          p('<b>Numerical criterion.</b> The development establishes a smooth numerical freeness criterion using the minimization, growth, center-exclusion and lifting argument.'),
          p('<b>Mixed intersections.</b> For A = L<sub>1</sub> + ... + L<sub>s</sub>, positivity and integrality of the mixed intersections give A<sup>d</sup> &middot; W &ge; s<sup>d</sup> &ge; (n+1)<sup>d</sup> on every positive-dimensional integral subvariety W. The numerical criterion then supplies the mixed statement.'),
          p('<b>Classical specialization.</b> FCSolution.lean derives the classical declaration from the mixed declaration. The proof is in the package; the statement-only reference has intentional holes.'),
          p('5. Entry points and checks', 'HeadingCustom'),
          p('<b>Main:</b> FujitaPublication.fujita<br/><b>Variant:</b> FujitaPublication.variants.mixed'),
          p('The two proof directories contain identical shared Lean sources. Lean is pinned to v4.35.0-rc3, and the dependency lock fixes Mathlib. The target axiom audit reports only propext, Classical.choice and Quot.sound.'),
          p('Challenge and FCSolution are compared by the pinned native Comparator. The current run, source hashes, export hashes and sandbox setting are recorded in verification/. The macOS run explicitly disables the Linux-only sandbox.'),
          p('6. Scope of the FC draft', 'HeadingCustom'),
          p('FClikelean/Fujita.lean is a 120-line standalone proposal with six definitions and two statement holes. It imports only FormalConjecturesUtil and has no dependency on the proof project.'),
          p('<b>Remaining connection.</b> The FC draft uses local Cartier equations and differential lattices. The proof library uses a sheaf-based representation. A Lean dictionary between these representations is still required before the proof can be linked as a verified proof of this exact FC file.'),
          p('<b>Header audit.</b> The mathematical body and the FC audit with the standard FC header pass. The retained short project copyright header is rejected by FC\'s strict copyright linter. No linter is disabled.'),
          p('This is a local package. No CI, push, publication or independent mathematical peer review is claimed. The F2 publication target is outside its scope.', 'SmallCustom'),
          p('Developed by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex. Project code is Apache-2.0; vendored libraries retain their notices and licenses, including MIT for SGA.', 'SmallCustom')]
doc = SimpleDocTemplate(str(OUT), pagesize=(210*mm,297*mm), leftMargin=20*mm, rightMargin=20*mm,
                        topMargin=20*mm, bottomMargin=24*mm, title='Fujita freeness and its mixed variant',
                        author='Kenta Kitamura')
doc.build(story, onFirstPage=footer, onLaterPages=footer)
print(str(OUT))
