"""Read reviewer rev1186c's certificates (`data/certs_rev1186c.json`, committed in the interface commit 47bee1f) into
this lane's form/theta representation.  Starting data only: every statement made about the output is re-checked by
this lane's own code (sdpmodel.py, verify_certs.py)."""
import io
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json
from fractions import Fraction as Fr

from sdpmodel import EXACT, load_grid

SLAB_KEY = {2: "slab[1/5,3/10]", 3: "slab[3/10,2/5]", 4: "slab[2/5,9/20]", 5: "slab[9/20,1/2]"}


def convert_key(k):
    t = k[0]
    if t == "lin":
        if k[1] == "y":
            return ["y", k[2]]
        if k[1] == "1-y":
            return ["o", k[2]]
        if k[1] == "m-lo":
            return ["ml"]
        if k[1] == "hi-m":
            return ["hm"]
    if t == "mhm":
        return ["mhm"]
    m = {"ym-lo": "yml", "om-lo": "oml", "yhi-m": "yhm", "ohi-m": "ohm", "yy": "yy", "oo": "oo", "yo": "yo"}
    if t in m:
        return [m[t]] + list(k[1:])
    if t == "tri":
        return ["tri"] + list(k[1:])
    raise KeyError(k)


def load_rev(region):
    """-> (grid name, B, theta dict {(i,j): Fraction}, forms_mu list of (form, Fraction))"""
    c = json.load(io.open(EXACT / "data" / "certs_rev1186c.json", encoding="utf-8"))
    s = c["slabs"][SLAB_KEY[region]]
    gname = s["grid"].upper()
    G = load_grid(gname)
    assert s["pts"] == G.pts
    theta = {}
    cut_list = G.cuts()
    assert len(cut_list) == len(s["cuts"]) == len(s["theta"])
    for (i, j), ent, th in zip(cut_list, s["cuts"], s["theta"]):
        assert ent[0] == i and ent[1] == j, (ent, i, j)
        assert ent[2] == G.sgn[i] * G.sgn[j]
        assert Fr(ent[3]) == G.ain(i, j) and Fr(ent[4]) == G.aout(i, j)
        theta[(i, j)] = Fr(th)
    forms = []
    for k, v in s["mu"]:
        forms.append((convert_key(k), Fr(v)))
    return gname, Fr(s["B"]), theta, forms
