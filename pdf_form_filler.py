import io
import re
import sys
from collections import defaultdict
from datetime import datetime
from decimal import Decimal
from pathlib import Path
from typing import NamedTuple

import pdfplumber
from pypdf import PdfReader, PdfWriter
from reportlab.pdfbase.pdfmetrics import stringWidth
from reportlab.pdfgen import canvas

FONT = "Helvetica"
FONT_SIZE = 9
MIN_FONT_SIZE = 6
CELL_PADDING = 4
INITIAL_FONT_SIZE = 10
INITIAL_GAP = 4

DATE_INPUTS = ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%d.%m.%Y", "%d %m %Y")
DATE_OUTPUT = "%d-%m-%Y"

FIXED_VALUES = {
    "nationality": "South African",
    "marital_status": "Single",
    "adults": "Two",
    "children": "None",
    "pets": "None",
    "dated_at": "Table View",
    "year_suffix": "26",
}

BOXES = [
    ("first", "Full name", "full_name"),
    ("first", "Maiden name (if applicable)", "maiden_name"),
    ("first", "Identity / passport number", "id_number"),
    ("first", "Date of birth", "dob"),
    ("first", "Nationality", "nationality"),
    ("first", "Marital status", "marital_status"),
    ("first", "Home telephone", "cellular"),
    ("first", "Cellular", "cellular"),
    ("first", "Email", "email"),
    ("first", "Physical address", "physical_address"),
    ("first", "Postal address", "postal_address"),
    ("first", "Next of kin", "next_of_kin"),
    ("first", "contact number", "next_of_kin_number"),
    ("first", "Rental paid", "rental_paid"),
    ("first", "How long have you rented there?", "rented_how_long"),
    ("first", "Name of property practitioner / landlord", "landlord_name"),
    ("first", "Contact number", "landlord_contact"),
    ("first", "Bank", "bank"),
    ("first", "Branch", "branch"),
    ("first", "Branch code", "branch_code"),
    ("first", "Account number", "account_number"),
    ("first", "Type of account", "account_type"),
    ("first", "Occupation", "occupation"),
    ("first", "Current employer", "employer"),
    ("first", "Employer's address", "employer_address"),
    ("first", "Period of employment", "period_of_employment"),
    ("first", "Gross monthly salary (before deductions and tax)", "gross_salary"),
    ("first", "Nett monthly salary", "nett_salary"),
    ("first", "Currently monthly expenses", "monthly_expenses"),
    ("general", "Number of adults", "adults"),
    ("general", "Number of children", "children"),
    ("general", "Number of pets owned", "pets"),
]

SECOND_APPLICANT_HEADING = "DETAILS OF THE SECOND PERSON"
GENERAL_DETAILS_HEADING = "GENERAL DETAILS"
FIRST_APPLICANT_NAME_LABEL = "FULL NAME ( First Applicant)"
INITIAL_WORD = "Initial"


class Cell(NamedTuple):
    page: int
    section: str
    top: int
    bottom: int
    x0: float
    x1: float
    text: str
    words: list


class Placement(NamedTuple):
    page: int
    x: float
    baseline: float
    text: str
    size: float
    box: tuple


def clean(value):
    return str(value or "").strip()


def squash(text):
    return "".join(text.split())


def fmt_date(raw):
    for pattern in DATE_INPUTS:
        try:
            return datetime.strptime(raw, pattern).strftime(DATE_OUTPUT)
        except ValueError:
            continue
    raise ValueError(f"Unrecognised date: {raw!r}")


def to_number(raw):
    return Decimal(re.sub(r"[^\d.]", "", str(raw)))


def money(value):
    return f"{value:,.2f}".replace(",", " ").removesuffix(".00")


def resolve_expenses(details, notes):
    total = clean(details.get("monthly_expenses"))
    items = details.get("expenses_itemised") or {}
    amounts = items.values() if isinstance(items, dict) else items
    summed = sum((to_number(amount) for amount in amounts), Decimal(0))

    if total:
        if items and to_number(total) != summed:
            notes.append(
                f"Expenses: you gave a total of {total} but the itemised expenses "
                f"add up to {money(summed)}. Used your total."
            )
        return total
    if items:
        notes.append(f"Expenses: no total given, used the itemised sum {money(summed)}.")
        return money(summed)
    return ""


def collect_values(details, notes):
    values = defaultdict(str, {key: clean(value) for key, value in details.items()})
    values.update(FIXED_VALUES)

    names = (values["first_name"], values["middle_names"], values["last_name"])
    values["full_name"] = " ".join(part for part in names if part)
    if values["dob"]:
        values["dob"] = fmt_date(values["dob"])

    kin, relationship = values["next_of_kin_name"], values["next_of_kin_relationship"]
    values["next_of_kin"] = f"{kin} ({relationship})" if kin and relationship else kin

    if values["employed_since"]:
        values["period_of_employment"] = f"Since {values['employed_since']}"
    values["monthly_expenses"] = resolve_expenses(details, notes)

    for number, vehicle in enumerate((details.get("vehicles") or [])[:3], 1):
        values[f"vehicle_{number}_type"] = clean(vehicle.get("type"))
        values[f"vehicle_{number}_registration"] = clean(vehicle.get("registration"))

    holder = values["account_holder"]
    if holder and holder.lower() != values["full_name"].lower():
        notes.append(f"Banking: account holder {holder!r} differs from the applicant {values['full_name']!r}.")
    if details.get("occupants"):
        notes.append("Occupants: this form has no list of people staying, so no occupants were written.")

    answers = {"judgements": "no", "debt_review": "no"}
    if details.get("owns_property") is not None:
        answers["owner"] = "yes" if details["owns_property"] else "no"
    if details.get("self_employed") is not None:
        answers["self_employed"] = "yes" if details["self_employed"] else "no"
    return values, answers


def find_phrase(pdf, phrase):
    for number, page in enumerate(pdf.pages):
        matches = page.search(phrase, regex=False)
        if matches:
            return number, matches[0]
    raise ValueError(f"Could not find {phrase!r} on this form. Is it the right form?")


def merge_close(positions):
    merged = []
    for position in sorted(positions):
        if not merged or position - merged[-1] > 2:
            merged.append(position)
    return merged


def read_cells(pdf):
    second_page, second = find_phrase(pdf, SECOND_APPLICANT_HEADING)
    general_page, general = find_phrase(pdf, GENERAL_DETAILS_HEADING)

    def section_of(page, top):
        if (page, top) < (second_page, second["top"]):
            return "first"
        if (page, top) < (general_page, general["top"]):
            return "second"
        return "general"

    cells = []
    for number, page in enumerate(pdf.pages):
        words = page.extract_words()
        borders = [r for r in page.rects if r["x1"] - r["x0"] < 1.5 and r["bottom"] - r["top"] > 8]
        rows = defaultdict(list)
        for border in borders:
            rows[(round(border["top"]), round(border["bottom"]))].append(border["x0"])

        for (top, bottom), xs in rows.items():
            edges = merge_close(xs)
            for x0, x1 in zip(edges, edges[1:]):
                inside = [
                    w for w in words
                    if x0 <= (w["x0"] + w["x1"]) / 2 <= x1
                    and top - 1 <= (w["top"] + w["bottom"]) / 2 <= bottom + 1
                ]
                inside.sort(key=lambda w: (round(w["top"]), w["x0"]))
                text = " ".join(w["text"] for w in inside)
                cells.append(Cell(number, section_of(number, top), top, bottom, x0, x1, text, inside))

    cells.sort(key=lambda c: (c.page, c.top, c.x0))
    return cells


def find_label(cells, text, section, nth=0):
    matches = [c for c in cells if c.text == text and c.section == section]
    return matches[nth] if len(matches) > nth else None


def value_cell_of(cells, label):
    same_row = [
        c for c in cells
        if c.page == label.page and c.top == label.top and c.bottom == label.bottom and c.x0 >= label.x1 - 1
    ]
    return min(same_row, key=lambda c: c.x0) if same_row else None


def cell_box(cell):
    return (cell.x0, cell.top, cell.x1, cell.bottom)


def fit_font_size(text, width):
    size = FONT_SIZE
    while size > MIN_FONT_SIZE and stringWidth(text, FONT, size) > width:
        size -= 0.5
    return size


def write_in_cell(cell, text, placements, notes):
    if cell.section == "second":
        raise RuntimeError("Refusing to write in the second applicant section.")
    start = max([cell.x0 + CELL_PADDING] + [w["x1"] + 3 for w in cell.words])
    width = cell.x1 - CELL_PADDING - start
    size = fit_font_size(text, width)
    if stringWidth(text, FONT, size) > width:
        notes.append(f"'{text}' is too long for its box and may run over the edge.")
    baseline = (cell.top + cell.bottom) / 2 + size * 0.35
    placements.append(Placement(cell.page, start, baseline, text, size, cell_box(cell)))


def write_beside(cells, label_cell, label_text, text, placements, notes):
    if not text:
        return
    target = value_cell_of(cells, label_cell) if label_cell else None
    if target is None:
        notes.append(f"Could not find the box '{label_text}', so '{text}' was not written.")
        return
    write_in_cell(target, text, placements, notes)


def place_boxes(cells, values, placements, notes):
    for section, label_text, key in BOXES:
        label_cell = find_label(cells, label_text, section)
        write_beside(cells, label_cell, label_text, values[key], placements, notes)


def place_vehicles(cells, values, placements, notes):
    for number in (1, 2, 3):
        type_text = f"{number}. Type"
        type_label = find_label(cells, type_text, "general")
        write_beside(cells, type_label, type_text, values[f"vehicle_{number}_type"], placements, notes)

        registration_label = find_label(cells, "registration number", "general", nth=number - 1)
        registration = values[f"vehicle_{number}_registration"]
        write_beside(cells, registration_label, "registration number", registration, placements, notes)


def place_answers(cells, answers, placements, notes):
    yes_no = [c for c in cells if c.text == "yes no"]
    first = [c for c in yes_no if c.section == "first"]
    general = [c for c in yes_no if c.section == "general"]
    if len(first) < 2 or len(general) < 2:
        notes.append("Could not find all the yes/no boxes, so no yes/no answers were marked.")
        return

    targets = {
        "owner": first[0],
        "self_employed": first[1],
        "judgements": general[0],
        "debt_review": general[1],
    }
    for name, answer in answers.items():
        cell = targets[name]
        word = next((w for w in cell.words if w["text"] == answer), None)
        if word is None:
            notes.append(f"Could not find the '{answer}' option for {name}.")
            continue
        baseline = (cell.top + cell.bottom) / 2 + FONT_SIZE * 0.35
        placements.append(Placement(cell.page, word["x1"] + 3, baseline, "X", FONT_SIZE, cell_box(cell)))


def place_signing(pdf, cells, values, placements, notes):
    page_number, name_label = find_phrase(pdf, FIRST_APPLICANT_NAME_LABEL)
    first_block = [c for c in cells if c.page == page_number and c.top < name_label["top"]]

    for label_text, key in (("DATED AT (place)", "dated_at"), ("20", "year_suffix")):
        label_cell = find_label(first_block, label_text, "general")
        write_beside(first_block, label_cell, label_text, values[key], placements, notes)

    lines = [
        r for r in pdf.pages[page_number].rects
        if r["x1"] - r["x0"] > 100
        and r["bottom"] - r["top"] < 1.5
        and r["top"] < name_label["top"]
        and abs(r["x0"] - name_label["x0"]) < 10
    ]
    if not lines or not values["full_name"]:
        return
    line = max(lines, key=lambda r: r["top"])
    size = fit_font_size(values["full_name"], line["x1"] - line["x0"] - 6)
    box = (line["x0"], line["top"] - 14, line["x1"], line["top"] + 1)
    placements.append(Placement(page_number, line["x0"] + 3, line["top"] - 3, values["full_name"], size, box))


def place_initials(pdf, initials, placements, notes):
    width = stringWidth(initials, FONT, INITIAL_FONT_SIZE)
    for number, page in enumerate(pdf.pages):
        matches = page.search(INITIAL_WORD, regex=False)
        if not matches:
            continue
        if len(matches) > 1:
            notes.append(f"Page {number + 1} has {len(matches)} '{INITIAL_WORD}' labels. Used the last one.")
        word = matches[-1]
        x = word["x0"] - INITIAL_GAP - width
        box = (x - 2, word["top"] - 3, word["x0"], word["bottom"] + 3)
        placements.append(Placement(number, x, word["bottom"] - 1.5, initials, INITIAL_FONT_SIZE, box))
    if not any(p.text == initials for p in placements):
        notes.append(f"No '{INITIAL_WORD}' label found, so no initials were written.")


def make_overlay(page, items):
    buffer = io.BytesIO()
    height = float(page.mediabox.height)
    pen = canvas.Canvas(buffer, pagesize=(float(page.mediabox.width), height))
    for item in items:
        pen.setFont(FONT, item.size)
        pen.drawString(item.x, height - item.baseline, item.text)
    pen.save()
    buffer.seek(0)
    return PdfReader(buffer)


def text_in(page, box):
    x0, top, x1, bottom = box
    area = (max(x0, 0), max(top, 0), min(x1, page.width), min(bottom, page.height))
    return squash(page.crop(area).extract_text() or "")


def verify(blank, out_path, cells, placements):
    problems = []
    with pdfplumber.open(blank) as before, pdfplumber.open(out_path) as after:
        for item in placements:
            found = text_in(after.pages[item.page], item.box)
            if squash(item.text) not in found:
                problems.append(f"Page {item.page + 1}: expected {item.text!r}, found {found!r}")
        for cell in cells:
            if cell.section == "second" and cell.text != INITIAL_WORD:
                box = cell_box(cell)
                if text_in(before.pages[cell.page], box) != text_in(after.pages[cell.page], box):
                    problems.append(f"Page {cell.page + 1}: second applicant box '{cell.text}' changed")
    if problems:
        print("VERIFY FAILED")
        for problem in problems:
            print(" -", problem)
        sys.exit(1)
    print(f"Verified {len(placements)} entries; the second applicant section is untouched.")


def fill(blank, details, out_dir):
    blank, out_dir = Path(blank), Path(out_dir)
    out_path = out_dir / blank.name
    if out_path.resolve() == blank.resolve():
        sys.exit("Output would overwrite the blank PDF. Choose a different out folder.")

    notes = []
    placements = []
    values, answers = collect_values(details, notes)

    with pdfplumber.open(blank) as pdf:
        cells = read_cells(pdf)
        place_boxes(cells, values, placements, notes)
        place_vehicles(cells, values, placements, notes)
        place_answers(cells, answers, placements, notes)
        place_signing(pdf, cells, values, placements, notes)
        if values["first_name"] and values["last_name"]:
            initials = (values["first_name"][0] + values["last_name"][0]).upper()
            place_initials(pdf, initials, placements, notes)

    writer = PdfWriter(clone_from=PdfReader(blank))
    for number, page in enumerate(writer.pages):
        items = [p for p in placements if p.page == number]
        if items:
            page.merge_page(make_overlay(page, items).pages[0])

    out_dir.mkdir(parents=True, exist_ok=True)
    with open(out_path, "wb") as handle:
        writer.write(handle)

    verify(blank, out_path, cells, placements)
    if notes:
        print("Check these:")
        for note in notes:
            print(" -", note)
    return out_path


def render_pages(pdf_path, folder, resolution=90):
    pdf_path, folder = Path(pdf_path), Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    paths = []
    with pdfplumber.open(pdf_path) as pdf:
        for number, page in enumerate(pdf.pages, 1):
            path = folder / f"{pdf_path.stem}_page{number}.png"
            page.to_image(resolution=resolution).save(path)
            paths.append(path)
    return paths
