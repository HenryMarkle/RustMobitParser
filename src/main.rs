mod tokens;
mod ast;

use std::{path::PathBuf, fs::{read_to_string, write}};
use simple_logger::SimpleLogger;
use log::{LevelFilter, debug, error};

use clap::Parser;
use anyhow;

#[derive(Parser)]
#[command(author = "Henry Markle")]
#[command(about = "a Lingo parser", long_about = None)]
struct ParseCli {
    /// Gives the resulted tokens
    #[arg(short, long, value_name = "TOKENIZE", default_value_t = false)]
    tokenize: bool,

    /// Parse Lingo expression into JSON
    #[arg(short, long, value_name = "JSON", default_value_t = false)]
    json: bool,

    /// Format output
    #[arg(short, long, value_name = "PRETTY", default_value_t = true)]
    pretty: bool,

    /// Specify a text file for input
    #[arg(short, long, value_name = "FILE")]
    file: Option<PathBuf>,

    /// Specify a file to dumb the output into
    #[arg(short, long, value_name = "OUT FILE")]
    out: Option<PathBuf>,

    /// Provide Lingo expression as input
    input: Option<String>
}

fn main() -> anyhow::Result<()> {
    _ = SimpleLogger::new()
        .with_level(LevelFilter::Debug)
        .with_colors(true)
        .init()
        .expect("failed to initialize the logger");

    debug!("program begin");

    let cli = ParseCli::parse();

    let file_specified = cli.file.is_some();
    let input_specified = cli.input.is_some();

    if file_specified && input_specified {
        println!("cannot specify a file while also give an input string");
        return Err(anyhow::anyhow!("cannot specify file and console as input"));
    }

    if let Some(path) = cli.file {
        match read_to_string(&path) {
            Ok(text) => {
                let token_res = tokens::tokenize(&text);

                match token_res {
                    Ok(tokens) => {
                        if cli.tokenize {
                            if let Some(out_path) = cli.out {
                                if cli.pretty {
                                    write(out_path, format!("{:#?}", tokens))?;
                                } else {
                                    write(out_path, format!("{:?}", tokens))?;
                                }
                            } else {
                                if cli.pretty {
                                    println!("result:\n\n{:?}", tokens);
                                } else {
                                    println!("result:\n\n{:#?}", tokens);
                                }
                            }
                            return Ok(());
                        }

                        match ast::parse_tokens(&tokens) {
                            Ok(node) => {
                                if let Some(out_path) = cli.out {
                                    if cli.json {
                                        if cli.pretty {
                                            write(out_path, node.to_json_string_pretty())?;
                                        } else {
                                            write(out_path, node.to_json_string())?;
                                        }
                                    } else {
                                        if cli.pretty {
                                            write(out_path, format!("{:#?}", node))?;
                                        } else {
                                            write(out_path, format!("{:?}", node))?;
                                        }
                                    }
                                } else {
                                    if cli.json {
                                        if cli.pretty {
                                            println!("result:\n\n{}", node.to_json_string_pretty());
                                        } else {
                                            println!("result:\n\n{}", node.to_json_string());
                                        }
                                    } else {
                                        if cli.pretty {
                                            println!("result:\n\n{:#?}", node);
                                        } else {
                                            println!("result:\n\n{:?}", node);
                                        }
                                    }
                                }
                            },

                            Err(parse_err) => {
                                error!("failed to parse tokens: {:#?}", parse_err);
                                println!("error while parsing file");
                            }
                        }
                    },

                    Err(token_err) => {
                        error!("failed to tokenize input: {:#?}", token_err);
                        println!("error while parsing file");
                    }
                }
            },

            Err(read_err) => {
                error!("failed to read file at path \"{:?}\": {:#?}", &path, read_err);
                println!("failed to read file");
            }
        }
    } else if let Some(input) = cli.input {
        let token_res = tokens::tokenize(&input);

        match token_res {
            Ok(tokens) => {
                if cli.tokenize {
                    if let Some(out_path) = cli.out {
                        if cli.pretty {
                            write(out_path, format!("{:#?}", tokens))?;
                        } else {
                            write(out_path, format!("{:?}", tokens))?;
                        }
                    } else {
                        if cli.pretty {
                            println!("result:\n\n{:#?}", tokens);
                        } else {
                            println!("result:\n\n{:?}", tokens);
                        }
                    }
                    return Ok(());
                }

                match ast::parse_tokens(&tokens) {
                    Ok(node) => {
                        if let Some(out_path) = cli.out {
                            if cli.json {
                                if cli.pretty {
                                    write(out_path, node.to_json_string_pretty())?;
                                } else {
                                    write(out_path, node.to_json_string())?;
                                }
                            } else {
                                if cli.pretty {
                                    write(out_path, format!("{:#?}", node))?;
                                } else {
                                    write(out_path, format!("{:?}", node))?;
                                }
                            }
                        } else {
                            if cli.json {
                                if cli.pretty {
                                    println!("result:\n\n{}", node.to_json_string_pretty());
                                } else {
                                    println!("result:\n\n{}", node.to_json_string());
                                }
                            } else {
                                if cli.pretty {
                                    println!("result:\n\n{:#?}", node);
                                } else {
                                    println!("result:\n\n{:?}", node);
                                }
                            }
                        }
                    },

                    Err(parse_err) => {
                        error!("failed to parse tokens: {:#?}", parse_err);
                        println!("error while parsing input");
                    }
                }
            },

            Err(token_err) => {
                error!("failed to tokenize input: {:#?}", token_err);
                println!("error while parsing input");
            }
        }
    }

    debug!("program terminated");

    Ok(())
}
