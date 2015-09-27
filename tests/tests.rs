extern crate serde_json;
extern crate regex_dfa;

use regex_dfa::Program;
use serde_json::Value;

const INPUT: &'static str = include_str!("tests.json");

#[test]
fn external_tests() {
    let val: Value = serde_json::from_str(INPUT).unwrap();
    let tests = val.as_array().unwrap();
    for test in tests {
        let test = test.as_object().unwrap();
        let status = test.get("status").unwrap().as_string().unwrap();
        if test.get("ignore").is_some() {
            continue;
        }

        if status == "MATCH" {
            let re_str = test.get("pattern").unwrap().as_string().unwrap();
            let text = test.get("text").unwrap().as_string().unwrap();
            println!("re: {:?}, text: {:?}", re_str, text);
            let range_arr = test.get("full_match").unwrap().as_array().unwrap();
            let range = (
                range_arr[0].as_u64().unwrap() as usize,
                range_arr[1].as_u64().unwrap() as usize
            );

            let prog = Program::from_regex(re_str).unwrap();
            let result = prog.shortest_match(text);
            assert!(result.is_some());
            let result = result.unwrap();
            assert_eq!(result.0, range.0);
            assert!(result.0 <= range.0);
        }
    }
}

