extern void zero_out<T>(inout T x);
void run() {
  mutable_packet(4096) pin;
  readPacket(pin);
  error last;
  {{ IM }} metas_;
  {{ IH }} hdrs;
  ingress_intrinsic_metadata_t igmd;
  {{ declare("ip") }};
  last = error.NoError;
  ip.apply(pin, hdrs, metas_, igmd, last);
  ingress_intrinsic_metadata_from_parser_t ig_intr_from_prsr;
  zero_out(ig_intr_from_prsr);
  if (last != error.NoError)
    ig_intr_from_prsr.parser_err = 16w1;
  {{ declare("ig") }};
  ingress_intrinsic_metadata_for_deparser_t ig_intr_md_for_dprsr;
  zero_out(ig_intr_md_for_dprsr);
  ingress_intrinsic_metadata_for_tm_t ig_intr_md_for_tm;
  zero_out(ig_intr_md_for_tm);
  ig.apply(hdrs, metas_,
           igmd,
           ig_intr_from_prsr,
           ig_intr_md_for_dprsr,
           ig_intr_md_for_tm);
}