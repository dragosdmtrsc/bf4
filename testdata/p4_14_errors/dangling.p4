header_type data_t {
    fields {
        f1 : 32;
        f2 : 32;
    } }
action _nop() {}
metadata data_t m;
table t1 { actions { _nop; } }
table t2 { actions {  _nop; } }
parser start {
    return ingress; }
control ingress {
    if (m.f1 == 32w0) {
        if (m.f2 == 32w0) {
            apply(t1);
        }
    } else {
        apply(t2);
    }
}