#include <core.p4>
#include <v1model.p4>

struct data_t {
    bit<32> f1;
    bit<32> f2;
}

struct metadata {
    @name(".m") 
    data_t m;
}

struct headers {
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".start") state start {
        transition accept;
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".NoAction") action NoAction_0() {
    }
    @name(".NoAction") action NoAction_3() {
    }
    @name("._nop") action _nop() {
    }
    @name("._nop") action _nop_2() {
    }
    @name(".t1") table t1_0 {
        actions = {
            _nop();
            @defaultonly NoAction_0();
        }
        default_action = NoAction_0();
    }
    @name(".t2") table t2_0 {
        actions = {
            _nop_2();
            @defaultonly NoAction_3();
        }
        default_action = NoAction_3();
    }
    apply {
        if (meta.m.f1 == 32w0)  {
            if (meta.m.f2 == 32w0)  {
                t1_0.apply();
            } 
        } 
        else  {
            t2_0.apply();
        }
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

V1Switch<headers, metadata>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

