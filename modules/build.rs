extern crate prost_build;
extern crate protoc_rust;

use protoc_rust::Customize;

fn main() {

    prost_build::compile_protos(&["src/proto/connection.proto"], &["src/proto"]).unwrap();

    protoc_rust::run(protoc_rust::Args {
        out_dir: "src/proto",
        input: &["src/proto/connection.proto"],
        includes: &["src/proto"],
        customize: Customize {
            ..Default::default()
        },
    }).expect("protoc");
}
